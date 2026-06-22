const Unprocessed = @import("parser.zig");
const std = @import("std");
const parser = @import("parser.zig");

pub const ProcessorError = error{
    UnsupportedValuation,
};

pub const State = u32;
pub const Symbol = u32;
pub const RuleName = u32;
pub const PhaseName = u32;
pub const Conf = struct {
    state: State,
    stack: []Symbol,
    phase: PhaseName,
};

pub const InternalRule = struct { from: State, top: Symbol, to: State, new_top: ?Symbol, new_tail: ?Symbol };

pub const CallRule = struct { from: State, top: Symbol, to: State, new_top: Symbol, new_tail: Symbol };

pub const RetRule = struct { from: State, top: Symbol, to: State };

pub const SMRule = struct { from: State, old_phase: PhaseName, new_phase: PhaseName, to: State };

pub const Rule = union(enum) {
    int: InternalRule,
    call: CallRule,
    ret: RetRule,
    sm: SMRule,
};

pub const LabelledRule = struct {
    label: RuleName,
    rule: Rule,
};

pub fn Pair(comptime F: type, comptime S: type) type {
    return struct {
        first: F,
        second: S,
    };
}

pub const SM_PDS = struct {
    states: []const State,
    alphabet: []const Symbol,
    rules: std.array_list.Managed(LabelledRule),
    end_of_stack: Symbol,

    init_conf: Conf,

    phases: *PhaseProcessor,
};

pub fn Set(comptime T: type) type {
    return struct { items: std.AutoArrayHashMap(T, void) };
}

pub fn SetContext(comptime T: type) type {
    return struct {
        pub fn hash(_: @This(), v: Set(T)) u32 {
            var sum: u32 = 0;
            for (v.items.keys()) |item| {
                sum ^= std.hash.Murmur3_32.hashUint32(item);
            }
            return sum;
        }

        pub fn eql(_: @This(), left: Set(T), right: Set(T), _: usize) bool {
            return left.items.count() == right.items.count() and blk: {
                for (left.items.keys()) |item| {
                    if (!right.items.contains(item)) {
                        break :blk false;
                    }
                }
                break :blk true;
            };
        }
    };
}

const RuleNameProcessor = struct {
    rule_map: std.StringArrayHashMap(RuleName),
    var rule_name_offset: RuleName = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{ .rule_map = std.StringArrayHashMap(RuleName).init(allocator) };
    }

    pub fn get_rule_name(self: *@This(), label: []const u8) !RuleName {
        return self.rule_map.get(label) orelse blk: {
            const name = rule_name_offset;
            rule_name_offset += 1;
            try self.rule_map.put(label, name);
            break :blk name;
        };
    }
};

pub const PhaseProcessor = struct {
    phase_map: std.ArrayHashMap(Set(RuleName), PhaseName, SetContext(RuleName), true),
    phase_values: std.AutoArrayHashMap(PhaseName, Set(RuleName)),

    var phase_name_offset: PhaseName = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{
            .phase_map = std.ArrayHashMap(Set(RuleName), PhaseName, SetContext(RuleName), true).init(allocator),
            .phase_values = std.AutoArrayHashMap(PhaseName, Set(RuleName)).init(allocator),
        };
    }

    pub fn get_phase_name(self: *@This(), label: Set(RuleName)) !PhaseName {
        return self.phase_map.get(label) orelse blk: {
            const name = phase_name_offset;
            phase_name_offset += 1;
            try self.phase_map.put(label, name);
            try self.phase_values.put(name, label);
            break :blk name;
        };
    }
};

pub const StateProcessor = struct {
    state_map: std.StringArrayHashMap(State),
    var state_name_offset: State = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{ .state_map = std.StringArrayHashMap(State).init(allocator) };
    }

    pub fn get_state_name(self: *@This(), label: []const u8) !State {
        return self.state_map.get(label) orelse blk: {
            const name = state_name_offset;
            state_name_offset += 1;
            try self.state_map.put(label, name);
            break :blk name;
        };
    }
};

pub const SymbolProcessor = struct {
    symbol_map: std.StringArrayHashMap(Symbol),
    symbol_names: std.AutoArrayHashMap(Symbol, []const u8),
    var symbol_name_offset: Symbol = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{
            .symbol_map = std.StringArrayHashMap(Symbol).init(allocator),
            .symbol_names = std.AutoArrayHashMap(Symbol, []const u8).init(allocator),
        };
    }

    pub fn get_symbol_name(self: *@This(), label: []const u8) !Symbol {
        return self.symbol_map.get(label) orelse blk: {
            const name = symbol_name_offset;
            symbol_name_offset += 1;
            try self.symbol_map.put(label, name);
            try self.symbol_names.put(name, label);
            break :blk name;
        };
    }
};

pub const LabellingFunction = struct {
    ap_dfas: std.StringArrayHashMap(std.AutoArrayHashMap(State, usize)),

    dfas: std.array_list.Managed(DFA),
    state_aps: std.AutoArrayHashMap(State, std.StringArrayHashMap(void)),

    pub const Labeller = *const fn ([]const u8, []const u8) bool;

    pub fn init(gpa: std.mem.Allocator, proc: *SM_PDS_Processor, formula: BranchCaret.Formula, func: Labeller, valuations: []const parser.Valuation) !LabellingFunction {
        var state_names = std.AutoHashMap(State, []const u8).init(gpa);
        defer state_names.deinit();

        var state_aps = std.AutoArrayHashMap(State, std.StringArrayHashMap(void)).init(gpa);
        errdefer {
            for (state_aps.keys()) |s| {
                state_aps.getPtr(s).?.deinit();
            }
            state_aps.deinit();
        }

        for (proc.states.state_map.keys()) |name| {
            const state = proc.states.state_map.get(name).?;
            try state_names.put(state, name);
            try state_aps.put(state, std.StringArrayHashMap(void).init(gpa));
        }

        const alphabet = proc.symbols.symbol_map.keys();

        var dfas = std.array_list.Managed(DFA).init(gpa);
        errdefer {
            for (dfas.items) |*dfa| {
                dfa.deinit();
            }
            dfas.deinit();
        }

        var unique_dfas = std.StringHashMap(usize).init(gpa);
        defer {
            var keyit = unique_dfas.keyIterator();
            while (keyit.next()) |k| {
                gpa.free(k.*);
            }
            unique_dfas.deinit();
        }

        var ap_dfas = std.StringArrayHashMap(std.AutoArrayHashMap(State, usize)).init(gpa);
        errdefer {
            for (ap_dfas.values()) |*v| {
                v.deinit();
            }
            ap_dfas.deinit();
        }

        for (valuations) |val| {
            const gop = try ap_dfas.getOrPut(val.ap);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(State, usize).init(gpa);
            }
            switch (val.val) {
                .state => |s| {
                    for (proc.states.state_map.keys()) |state_str| {
                        if (func(s, state_str)) {
                            const ap_set = state_aps.getPtr(proc.states.state_map.get(state_str).?).?;
                            try ap_set.*.put(val.ap, {});
                        }
                    }
                },
                .regular => |reg| {
                    const regstr = try std.fmt.allocPrint(gpa, "{f}", .{reg.regex.*});
                    defer gpa.free(regstr);

                    const dfa_gop = try unique_dfas.getOrPut(regstr);
                    if (!dfa_gop.found_existing) {
                        dfa_gop.key_ptr.* = try gpa.dupe(u8, regstr);
                        dfa_gop.value_ptr.* = dfas.items.len;
                        var new_nfa = try NFA.initFromRegex(gpa, reg.regex);
                        defer new_nfa.deinit();
                        try new_nfa.regToNfa();
                        // new_nfa.reverse();
                        const dfa = try new_nfa.determinize(gpa, alphabet);
                        try dfas.append(dfa);
                    }
                    if (reg.state == null) {
                        for (proc.states.state_map.keys()) |st| {
                            try gop.value_ptr.*.put(proc.states.state_map.get(st).?, dfa_gop.value_ptr.*);
                        }
                    } else {
                        for (proc.states.state_map.keys()) |st| {
                            // std.debug.print("{s}\n", .{st});
                            if (func(reg.state.?, st)) {
                                try gop.value_ptr.*.put(proc.states.state_map.get(st).?, dfa_gop.value_ptr.*);
                            }
                        }
                    }
                },
                else => {
                    return ProcessorError.UnsupportedValuation;
                    // var buf: [100]u8 = undefined;
                    // @panic(try std.fmt.bufPrint(&buf, "Unsupprorted valuation type {s}", .{@tagName(val.val)}));
                },
            }
        }

        try fillAps(&state_aps, formula, state_names, func);

        return LabellingFunction{
            .state_aps = state_aps,
            .ap_dfas = ap_dfas,
            .dfas = dfas,
        };
    }

    pub fn deinit(self: *@This()) void {
        for (self.dfas.items) |*dfa| {
            dfa.deinit();
        }
        self.dfas.deinit();

        for (self.state_aps.keys()) |s| {
            self.state_aps.getPtr(s).?.deinit();
        }
        self.state_aps.deinit();

        for (self.ap_dfas.values()) |*v| {
            v.deinit();
        }
        self.ap_dfas.deinit();
    }

    pub const strict: Labeller = struct {
        pub fn cmp(ap: []const u8, control_point: []const u8) bool {
            return std.mem.eql(u8, ap, control_point);
        }
    }.cmp;

    pub const substr: Labeller = struct {
        pub fn cmp(ap: []const u8, control_point: []const u8) bool {
            return std.mem.indexOf(u8, control_point, ap) != null;
        }
    }.cmp;

    pub const naive: Labeller = struct {
        pub fn cmp(ap: []const u8, control_point: []const u8) bool {
            const delim = std.mem.lastIndexOf(u8, control_point, "#").?;
            // std.debug.print("Comparing {s} and {s}: {}\n", .{ ap, control_point, std.mem.eql(u8, control_point[0..delim], ap) });
            return std.mem.eql(u8, control_point[0..delim], ap);
        }
    }.cmp;

    pub fn fillAps(
        state_aps: *std.AutoArrayHashMap(State, std.StringArrayHashMap(void)),
        formula: BranchCaret.Formula,
        state_names: std.AutoHashMap(State, []const u8),
        func: Labeller,
    ) !void {
        switch (formula) {
            .at => |at| {
                for (state_aps.keys()) |s| {
                    const name = state_names.get(s).?;
                    if (func(at.name, name)) {
                        try state_aps.getPtr(s).?.put(at.name, {});
                    }
                }
            },
            .top, .bot, .nat => {},
            .land => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .lor => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .arg => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .ara => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .arc => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .erg => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .era => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .erc => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .aug => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .aua => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .auc => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .eug => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .eua => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .euc => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .axg => |n| {
                try fillAps(state_aps, n.*, state_names, func);
            },
            .axa => |n| {
                try fillAps(state_aps, n.*, state_names, func);
            },
            .axc => |n| {
                try fillAps(state_aps, n.*, state_names, func);
            },
            .exg => |n| {
                try fillAps(state_aps, n.*, state_names, func);
            },
            .exa => |n| {
                try fillAps(state_aps, n.*, state_names, func);
            },
            .exc => |n| {
                try fillAps(state_aps, n.*, state_names, func);
            },
        }
    }

    // pub fn isAPinState(self: @This(), ap: []const u8, state: State) bool {
    //     const aps = self.getAPs(state);

    //     return aps.contains(ap);
    // }

    pub fn getAPs(self: @This(), state: State) std.StringArrayHashMap(void) {
        return self.state_aps.get(state).?;
    }
};

pub const PhaseTriple = struct {
    original_phase: PhaseName,
    to_remove: PhaseName,
    to_add: PhaseName,
};

pub const SM_PDS_Processor = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    rule_names: RuleNameProcessor,
    states: StateProcessor,
    symbols: SymbolProcessor,
    phase_names: PhaseProcessor,

    phase_combiner: std.AutoArrayHashMap(PhaseTriple, PhaseName),
    phases: std.AutoArrayHashMap(PhaseName, void),

    state_phases: std.AutoArrayHashMap(State, std.AutoArrayHashMap(PhaseName, void)),

    system: ?SM_PDS,

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator) @This() {
        return .{
            .system = null,

            .arena = arena,
            .gpa = gpa,

            .rule_names = RuleNameProcessor.init(arena),
            .states = StateProcessor.init(arena),
            .symbols = SymbolProcessor.init(arena),
            .phase_names = PhaseProcessor.init(arena),
            .phase_combiner = std.AutoArrayHashMap(PhaseTriple, PhaseName).init(gpa),
            .phases = std.AutoArrayHashMap(PhaseName, void).init(gpa),
            .state_phases = .init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.phase_combiner.deinit();
        self.phases.deinit();
        if (self.system) |*s| {
            s.rules.deinit();
        }
        for (self.state_phases.values()) |*m| {
            m.deinit();
        }
        self.state_phases.deinit();
    }

    pub fn process_state(self: *@This(), state: []const u8) !State {
        return try self.states.get_state_name(state);
    }

    pub fn process_symbol(self: *@This(), symbol: []const u8) !Symbol {
        return try self.symbols.get_symbol_name(symbol);
    }

    pub fn process_rule_name(self: *@This(), rule_name: []const u8) !RuleName {
        return try self.rule_names.get_rule_name(rule_name);
    }

    pub fn process_phase(self: *@This(), phase: []const []const u8) !PhaseName {
        var processed_phase = Set(RuleName){ .items = std.AutoArrayHashMap(RuleName, void).init(self.arena) };
        try processed_phase.items.ensureTotalCapacity(phase.len);
        for (phase) |r| {
            try processed_phase.items.put(try self.process_rule_name(r), {});
        }
        const name = try self.phase_names.get_phase_name(processed_phase);
        return name;
    }

    const ProcessingError = error{
        InvalidRule,
        SameStateInTwoProcesses,
    };

    fn simplify(gpa: std.mem.Allocator, rules: *std.array_list.Managed(LabelledRule), ini: Conf) !void {
        var ma = PostMA{};
        defer ma.deinit(gpa);

        var node_offset: u32 = 0;

        var cur: PostMA.Node = .{ .st = .{ .state = ini.state } };
        var acc = false;
        for (ini.stack, 0..) |sym, symi| {
            if (symi >= ini.stack.len - 1) {
                acc = true;
            }
            _ = try ma.addEdge(gpa, .{
                .from = cur,
                .symbol = .{ .symbol = sym },
                .to = .{ .int = .{ .id = node_offset, .accepting = acc } },
            });
            cur = .{ .int = .{ .id = node_offset, .accepting = acc } };
            node_offset += 1;
        }

        try ma.constructPostStar(gpa, rules.*);
        var rules_to_delete = std.ArrayList(usize).empty;
        defer rules_to_delete.deinit(gpa);
        for (rules.items, 0..) |rule, ri| {
            switch (rule.rule) {
                .int => |r| {
                    if (!ma.edges_by_head_sym.contains(.{
                        .state = .{ .st = .{ .state = r.from } },
                        .sym = .{ .symbol = r.top },
                    })) {
                        try rules_to_delete.append(gpa, ri);
                    }
                },
                .call => |r| {
                    if (!ma.edges_by_head_sym.contains(.{
                        .state = .{ .st = .{ .state = r.from } },
                        .sym = .{ .symbol = r.top },
                    })) {
                        try rules_to_delete.append(gpa, ri);
                    }
                },
                .ret => |r| {
                    if (!ma.edges_by_head_sym.contains(.{
                        .state = .{ .st = .{ .state = r.from } },
                        .sym = .{ .symbol = r.top },
                    })) {
                        try rules_to_delete.append(gpa, ri);
                    }
                },
                .sm => |r| {
                    if (!ma.edges_by_head.contains(.{
                        .st = .{ .state = r.from },
                    })) {
                        try rules_to_delete.append(gpa, ri);
                    }
                },
            }
        }

        var rdi = rules_to_delete.items.len;
        while (rdi > 0) {
            rdi -= 1;
            const ri = rules_to_delete.items[rdi];
            _ = rules.swapRemove(ri);
        }
    }

    pub fn process(self: *@This(), smpds: Unprocessed.SM_PDS, init_conf: Unprocessed.Conf) !void {
        var rules = std.array_list.Managed(LabelledRule).init(self.gpa);

        for (smpds.rules) |rule| {
            const processed_rule: Rule = switch (rule.typ) {
                Unprocessed.RuleType.internal => Rule{ .int = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .top = try self.process_symbol(rule.top orelse return ProcessingError.InvalidRule),
                    .new_top = if (rule.new_top) |_| try self.process_symbol(rule.new_top.?) else null,
                    .new_tail = if (rule.new_tail) |nt| try self.process_symbol(nt) else null,
                } },
                Unprocessed.RuleType.call => Rule{ .call = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .top = try self.process_symbol(rule.top orelse return ProcessingError.InvalidRule),
                    .new_top = try self.process_symbol(rule.new_top orelse return ProcessingError.InvalidRule),
                    .new_tail = try self.process_symbol(rule.new_tail orelse return ProcessingError.InvalidRule),
                } },
                Unprocessed.RuleType.ret => Rule{ .ret = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .top = try self.process_symbol(rule.top orelse return ProcessingError.InvalidRule),
                } },
                Unprocessed.RuleType.sm => Rule{ .sm = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .old_phase = try self.process_phase(rule.sm_l orelse return ProcessingError.InvalidRule),
                    .new_phase = try self.process_phase(rule.sm_r orelse return ProcessingError.InvalidRule),
                } },
            };
            const name = try self.process_rule_name(rule.name);
            try rules.append(LabelledRule{ .label = name, .rule = processed_rule });
        }

        var states = try self.arena.alloc(State, smpds.states.len);
        for (smpds.states, 0..) |s, j| {
            states[j] = try self.process_state(s);
        }

        var alphabet = try self.arena.alloc(Symbol, smpds.alphabet.len + 1);
        for (smpds.alphabet, 0..) |s, j| {
            alphabet[j] = try self.process_symbol(s);
        }
        alphabet[smpds.alphabet.len] = try self.process_symbol("#");

        const ini = try self.getInit(init_conf);
        try simplify(self.gpa, &rules, ini);

        self.system = SM_PDS{
            .rules = rules,
            .states = states,
            .alphabet = alphabet,
            .phases = &self.phase_names,
            .end_of_stack = alphabet[smpds.alphabet.len],
            .init_conf = ini,
        };

        const conf = try self.getInit(init_conf);
        _ = try self.getPhases(conf.phase);
        try self.computePhases(conf);
    }

    fn StackSet(comptime T: type) type {
        return struct {
            stack: std.ArrayList(T) = .{},
            set: std.AutoArrayHashMapUnmanaged(T, void) = .{},

            pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
                self.stack.deinit(gpa);
                self.set.deinit(gpa);
            }

            pub fn append(self: *@This(), gpa: std.mem.Allocator, item: T) !void {
                const gop = try self.set.getOrPut(gpa, item);
                if (gop.found_existing) return;
                return self.stack.append(gpa, item);
            }

            pub fn pop(self: *@This()) ?T {
                return self.stack.pop();
            }
        };
    }

    fn computePhases(self: *@This(), init_conf: Conf) !void {
        var stack = StackSet(struct { state: State, phase: PhaseName }){};
        defer stack.deinit(self.gpa);
        try stack.append(self.gpa, .{ .state = init_conf.state, .phase = init_conf.phase });

        while (stack.pop()) |cur| {
            const gop = try self.state_phases.getOrPutValue(cur.state, .init(self.gpa));
            try gop.value_ptr.put(cur.phase, {});
            const phase = self.phase_names.phase_values.get(cur.phase).?;
            for (self.system.?.rules.items) |rule| {
                if (phase.items.contains(rule.label)) {
                    switch (rule.rule) {
                        .sm => |r| {
                            const to_phase = self.phase_combiner.get(.{
                                .original_phase = cur.phase,
                                .to_add = r.new_phase,
                                .to_remove = r.old_phase,
                            });
                            if (to_phase) |tp| {
                                try stack.append(self.gpa, .{ .state = r.to, .phase = tp });
                            }
                        },
                        inline else => |r| try stack.append(self.gpa, .{ .state = r.to, .phase = cur.phase }),
                    }
                }
            }
        }
    }

    pub fn getInit(self: *@This(), init_conf: Unprocessed.Conf) !Conf {
        const state = try self.process_state(init_conf.state);
        var stack = try self.arena.alloc(Symbol, init_conf.stack.len);
        for (init_conf.stack, 0..) |s, i| {
            stack[i] = try self.process_symbol(s);
        }
        const phase = try self.process_phase(init_conf.phase);
        return Conf{
            .state = state,
            .stack = stack,
            .phase = phase,
        };
    }

    pub fn getPhases(self: *@This(), init_phase: PhaseName) !void {
        var visited_phases = &self.phases;

        var phase_stack = std.ArrayList(PhaseName){};
        defer phase_stack.deinit(self.gpa);

        try phase_stack.append(self.gpa, init_phase);
        while (phase_stack.pop()) |ph| {
            if (visited_phases.contains(ph)) {
                continue;
            }
            try visited_phases.put(ph, {});

            const phase = self.phase_names.phase_values.get(ph).?;
            rule_loop: for (self.system.?.rules.items) |r_labelled| {
                const r_name = r_labelled.label;
                if (!phase.items.contains(r_name)) continue :rule_loop;

                const rule = r_labelled.rule;
                switch (rule) {
                    .sm => |r| {
                        const old_phase = self.phase_names.phase_values.get(r.old_phase).?;
                        for (old_phase.items.keys()) |old_r| {
                            if (!phase.items.contains(old_r)) continue :rule_loop;
                        }

                        var tmp_phase = Set(RuleName){
                            .items = try phase.items.cloneWithAllocator(self.gpa),
                        };
                        defer tmp_phase.items.deinit();

                        for (old_phase.items.keys()) |old_r| {
                            _ = tmp_phase.items.swapRemove(old_r);
                        }

                        const new_phase = self.phase_names.phase_values.get(r.new_phase).?;
                        for (new_phase.items.keys()) |new_r| {
                            try tmp_phase.items.put(new_r, {});
                        }

                        const result_phase = Set(RuleName){
                            .items = try tmp_phase.items.cloneWithAllocator(self.arena),
                        };

                        const result_phase_name = try self.phase_names.get_phase_name(result_phase);
                        // std.debug.print("{}, {}, {}\n", .{ ph, r.old_phase, r.new_phase });
                        try self.phase_combiner.put(PhaseTriple{ .original_phase = ph, .to_remove = r.old_phase, .to_add = r.new_phase }, result_phase_name);
                        try phase_stack.append(self.gpa, result_phase_name);
                        try visited_phases.put(result_phase_name, {});
                    },
                    else => {},
                }
            }
        }
    }
};

pub fn Handle(tt: type) type {
    return packed struct {
        pub const T = tt;
        pub const nil: @This() = .{ .index = 0 };
        index: u32,
    };
}

pub const PostMA = struct {
    edges: std.ArrayList(Edge) = .empty,
    edges_by_head: std.AutoHashMapUnmanaged(Node, std.AutoArrayHashMapUnmanaged(Handle(Edge), void)) = .empty,
    edges_by_head_sym: std.AutoHashMapUnmanaged(struct { state: Node, sym: EdgeSymbol }, std.AutoArrayHashMapUnmanaged(Handle(Edge), void)) = .empty,
    edge_storage: std.AutoHashMapUnmanaged(Edge, Handle(Edge)) = .empty,
    edge_set: std.AutoHashMapUnmanaged(Handle(Edge), void) = .empty,
    eps_edges: std.AutoHashMapUnmanaged(AdditionalNode, std.AutoArrayHashMapUnmanaged(Handle(Edge), void)) = .empty,

    pub const StateNode = struct {
        state: State,
    };

    pub const InternalNode = struct {
        id: u32,
        accepting: bool,
    };

    pub const AdditionalNode = struct {
        trg: State,
        new_top: Symbol,
    };

    pub const Node = union(enum) {
        int: InternalNode,
        st: StateNode,
        add: AdditionalNode,
    };

    pub const EdgeSymbol = union(enum) {
        symbol: Symbol,
        // star: void,
        eps: void,
    };

    pub const Edge = struct {
        from: Node,
        symbol: EdgeSymbol,
        to: Node,
    };

    // const EdgeHead = struct {
    //     from: Node,
    //     symbol: ?EdgeSymbol,
    // };

    pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
        var it = self.edges_by_head.iterator();
        while (it.next()) |itt| {
            itt.value_ptr.deinit(gpa);
        }
        self.edges_by_head.deinit(gpa);
        var it2 = self.edges_by_head_sym.iterator();
        while (it2.next()) |itt| {
            itt.value_ptr.deinit(gpa);
        }
        self.edges_by_head_sym.deinit(gpa);
        var it3 = self.eps_edges.iterator();
        while (it3.next()) |itt| {
            itt.value_ptr.deinit(gpa);
        }
        self.eps_edges.deinit(gpa);
        self.edge_set.deinit(gpa);
        self.edge_storage.deinit(gpa);
        self.edges.deinit(gpa);
    }

    pub fn getEdge(self: @This(), edge: Handle(Edge)) Edge {
        return self.edges.items[edge.index];
    }

    pub fn storeEdge(self: *@This(), gpa: std.mem.Allocator, edge: Edge) !Handle(Edge) {
        const gop = try self.edge_storage.getOrPut(gpa, edge);
        if (!gop.found_existing) {
            const new_edge_i = self.edges.items.len;
            try self.edges.append(gpa, edge);
            gop.value_ptr.* = .{ .index = @intCast(new_edge_i) };
        }

        return gop.value_ptr.*;
    }

    pub fn addEdgePtr(self: *@This(), gpa: std.mem.Allocator, new_edge: Handle(Edge)) !bool {
        if (self.edge_set.contains(new_edge)) {
            return false;
        }
        try self.edge_set.put(gpa, new_edge, {});
        const edge = self.getEdge(new_edge);

        {
            const gop = try self.edges_by_head.getOrPutValue(gpa, edge.from, .empty);
            try gop.value_ptr.put(gpa, new_edge, {});
        }
        {
            const gop = try self.edges_by_head_sym.getOrPutValue(gpa, .{ .state = edge.from, .sym = edge.symbol }, .empty);
            try gop.value_ptr.put(gpa, new_edge, {});
        }

        if (edge.symbol == .eps and edge.to == .add) {
            const gop = try self.eps_edges.getOrPutValue(gpa, edge.to.add, .empty);
            try gop.value_ptr.put(gpa, new_edge, {});
        }
        return true;
    }

    pub fn addEdge(self: *@This(), gpa: std.mem.Allocator, edge: Edge) !Handle(Edge) {
        const new_edge = try self.storeEdge(gpa, edge);
        _ = try self.addEdgePtr(gpa, new_edge);
        return new_edge;
    }

    pub fn formatNode(
        self: @This(),
        writer: *std.Io.Writer,
        node: Node,
    ) !void {
        _ = self;
        switch (node) {
            .int => |s| {
                try writer.print("{s}{}", .{ if (s.accepting) "@" else "/", s.id });
            },
            .st => |s| {
                try writer.print("(", .{});
                try writer.print("{}", .{s.state});
                try writer.print(", ", .{});
                try writer.print("{}", .{s.phase});
                try writer.print(")", .{});
            },
        }
    }

    pub fn formatEdge(
        self: @This(),
        writer: *std.Io.Writer,
        edge: Edge,
    ) !void {
        try self.formatNode(writer, edge.from);
        try writer.print(" -[", .{});
        switch (edge.symbol) {
            .symbol => |s| {
                try writer.print("{}", .{s});
            },
            .star => {
                try writer.print("*", .{});
            },
        }
        try writer.print("]->{s} ", .{if (edge.accepting) ">" else ""});
        try self.formatNode(writer, edge.to);
    }

    pub fn StackSet(comptime T: type) type {
        return struct {
            stack: std.ArrayList(T) = .{},
            set: std.AutoArrayHashMapUnmanaged(T, void) = .{},

            pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
                self.stack.deinit(gpa);
                self.set.deinit(gpa);
            }

            pub fn append(self: *@This(), gpa: std.mem.Allocator, item: T) !void {
                const gop = try self.set.getOrPut(gpa, item);
                if (gop.found_existing) return;
                return self.stack.append(gpa, item);
            }

            pub fn pop(self: *@This()) ?T {
                return self.stack.pop();
            }
        };
    }

    fn constructPostStar(self: *@This(), gpa: std.mem.Allocator, rules: std.array_list.Managed(LabelledRule)) !void {
        var trans = StackSet(Handle(Edge)){};
        defer trans.deinit(gpa);

        var rules_by_lhs = std.AutoHashMapUnmanaged(struct { src: State, top: Symbol }, std.ArrayList(Handle(Rule))){};
        defer {
            var it = rules_by_lhs.valueIterator();
            while (it.next()) |itt| {
                itt.deinit(gpa);
            }
            rules_by_lhs.deinit(gpa);
        }
        var sm_rules_by_lhs = std.AutoHashMapUnmanaged(State, std.ArrayList(Handle(Rule))){};
        defer {
            var it = sm_rules_by_lhs.valueIterator();
            while (it.next()) |itt| {
                itt.deinit(gpa);
            }
            sm_rules_by_lhs.deinit(gpa);
        }

        for (rules.items, 0..) |r, ri| {
            const rh = Handle(Rule){
                .index = @intCast(ri),
            };
            switch (r.rule) {
                .int => |rr| {
                    const gop = try rules_by_lhs.getOrPutValue(gpa, .{ .src = rr.from, .top = rr.top }, .empty);
                    try gop.value_ptr.append(gpa, rh);
                },
                .call => |rr| {
                    const gop = try rules_by_lhs.getOrPutValue(gpa, .{ .src = rr.from, .top = rr.top }, .empty);
                    try gop.value_ptr.append(gpa, rh);
                },
                .ret => |rr| {
                    const gop = try rules_by_lhs.getOrPutValue(gpa, .{ .src = rr.from, .top = rr.top }, .empty);
                    try gop.value_ptr.append(gpa, rh);
                },
                .sm => |rr| {
                    const gop = try sm_rules_by_lhs.getOrPutValue(gpa, rr.from, .empty);
                    try gop.value_ptr.append(gpa, rh);
                },
            }
        }

        for (self.edges.items, 0..) |e, ei| {
            const eh = Handle(Edge){ .index = @intCast(ei) };

            if (e.from == .st and e.symbol == .symbol) {
                try trans.append(gpa, eh);
            }
        }

        while (trans.pop()) |eh| {
            const e = self.getEdge(eh);
            switch (e.symbol) {
                .symbol => |es| {
                    const sm_rules_lhs = sm_rules_by_lhs.get(e.from.st.state) orelse std.ArrayList(Handle(Rule)).empty;
                    for (sm_rules_lhs.items) |rh| {
                        const r = rules.items[rh.index].rule;
                        switch (r) {
                            .sm => |rule| {
                                const new_edge = try self.addEdge(gpa, .{
                                    .from = .{ .st = .{ .state = rule.to } },
                                    .symbol = .{ .symbol = es },
                                    .to = e.to,
                                });
                                try trans.append(gpa, new_edge);
                            },
                            else => unreachable,
                        }
                    }
                    const rules_lhs = rules_by_lhs.get(.{ .src = e.from.st.state, .top = es }) orelse std.ArrayList(Handle(Rule)).empty;
                    for (rules_lhs.items) |rh| {
                        const r = rules.items[rh.index].rule;
                        switch (r) {
                            .int => |rule| {
                                if (rule.new_top == null) {
                                    const new_edge = try self.addEdge(gpa, .{ .from = .{ .st = .{ .state = rule.to } }, .symbol = .eps, .to = e.to });
                                    try trans.append(gpa, new_edge);
                                } else if (rule.new_tail == null) {
                                    const new_edge = try self.addEdge(gpa, .{
                                        .from = .{ .st = .{ .state = rule.to } },
                                        .symbol = .{ .symbol = rule.new_top.? },
                                        .to = e.to,
                                    });
                                    try trans.append(gpa, new_edge);
                                } else {
                                    const new_edge = try self.addEdge(gpa, .{
                                        .from = .{ .st = .{ .state = rule.to } },
                                        .symbol = .{ .symbol = rule.new_top.? },
                                        .to = .{ .add = .{ .trg = rule.to, .new_top = rule.new_top.? } },
                                    });
                                    try trans.append(gpa, new_edge);
                                    const add_edge = try self.addEdge(gpa, .{
                                        .from = .{ .add = .{ .trg = rule.to, .new_top = rule.new_top.? } },
                                        .symbol = .{ .symbol = rule.new_tail.? },
                                        .to = e.to,
                                    });
                                    _ = add_edge;

                                    const eps_edges = self.eps_edges.get(.{ .trg = rule.to, .new_top = rule.new_top.? }) orelse std.AutoArrayHashMapUnmanaged(Handle(Edge), void).empty;
                                    for (eps_edges.keys()) |releh| {
                                        const rele = self.getEdge(releh);
                                        const new_add_edge = try self.addEdge(gpa, .{ .from = rele.from, .symbol = .{ .symbol = rule.new_tail.? }, .to = e.to });
                                        try trans.append(gpa, new_add_edge);
                                    }
                                }
                            },
                            .call => |rule| {
                                const new_edge = try self.addEdge(gpa, .{
                                    .from = .{ .st = .{ .state = rule.to } },
                                    .symbol = .{ .symbol = rule.new_top },
                                    .to = .{ .add = .{ .trg = rule.to, .new_top = rule.new_top } },
                                });
                                try trans.append(gpa, new_edge);
                                const add_edge = try self.addEdge(gpa, .{
                                    .from = .{ .add = .{ .trg = rule.to, .new_top = rule.new_top } },
                                    .symbol = .{ .symbol = rule.new_tail },
                                    .to = e.to,
                                });
                                _ = add_edge;

                                const eps_edges = self.eps_edges.get(.{ .trg = rule.to, .new_top = rule.new_top }) orelse std.AutoArrayHashMapUnmanaged(Handle(Edge), void).empty;
                                for (eps_edges.keys()) |releh| {
                                    const rele = self.getEdge(releh);
                                    const new_add_edge = try self.addEdge(gpa, .{ .from = rele.from, .symbol = .{ .symbol = rule.new_tail }, .to = e.to });
                                    try trans.append(gpa, new_add_edge);
                                }
                            },
                            .ret => |rule| {
                                const new_edge = try self.addEdge(gpa, .{ .from = .{ .st = .{ .state = rule.to } }, .symbol = .eps, .to = e.to });
                                try trans.append(gpa, new_edge);
                            },
                            .sm => {
                                unreachable;
                            },
                        }
                    }
                },
                .eps => {
                    const edges = self.edges_by_head.get(e.to) orelse std.AutoArrayHashMapUnmanaged(Handle(Edge), void).empty;
                    for (edges.keys()) |releh| {
                        const rele = self.getEdge(releh);

                        const new_add_edge = try self.addEdge(gpa, .{ .from = e.from, .symbol = rele.symbol, .to = rele.to });
                        try trans.append(gpa, new_add_edge);
                    }
                },
            }
        }
    }
};

pub const MA = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    edges_by_head: std.AutoHashMap(EdgeHead, std.AutoArrayHashMap(*const Edge, void)),
    edge_storage: std.AutoHashMap(Edge, *Edge),
    edge_set: std.AutoHashMap(*const Edge, void),

    pub const Node = union(enum) {
        state: State,
        internal: u32,
    };

    pub const EdgeSymbol = Symbol;

    pub const Edge = struct {
        from: Node,
        symbol: EdgeSymbol,
        to: Node,
    };

    const EdgeHead = struct {
        from: Node,
        symbol: ?EdgeSymbol,
    };

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator) @This() {
        return .{
            .arena = arena,
            .gpa = gpa,
            .edges_by_head = std.AutoHashMap(EdgeHead, std.AutoArrayHashMap(*const Edge, void)).init(gpa),
            .edge_set = std.AutoHashMap(*const Edge, void).init(gpa),
            .edge_storage = std.AutoHashMap(Edge, *Edge).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        var it = self.edges_by_head.valueIterator();
        while (it.next()) |el| {
            el.deinit();
        }
        self.edges_by_head.deinit();
        self.edge_set.deinit();
        self.edge_storage.deinit();
    }

    pub fn storeEdge(self: *@This(), edge: Edge) !*const Edge {
        const gop = try self.edge_storage.getOrPut(edge);
        if (gop.found_existing) {
            return gop.value_ptr.*;
        }
        const new_edge = try self.arena.create(Edge);
        new_edge.* = edge;
        gop.value_ptr.* = new_edge;
        return new_edge;
    }

    pub fn addEdgePtr(self: *@This(), new_edge: *const Edge) !bool {
        if (self.edge_set.contains(new_edge)) {
            return false;
        }
        try self.edge_set.put(new_edge, {});
        const edge = new_edge.*;

        {
            const head = EdgeHead{ .from = edge.from, .symbol = edge.symbol };

            const gop = try self.edges_by_head.getOrPut(head);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(new_edge, {});
        }
        {
            const head = EdgeHead{ .from = edge.from, .symbol = null };

            const gop = try self.edges_by_head.getOrPut(head);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(new_edge, {});
        }
        return true;
    }

    pub fn addEdge(self: *@This(), edge: Edge) !bool {
        const new_edge = try self.storeEdge(edge);
        return self.addEdgePtr(new_edge);
    }

    pub const PathResult = struct {
        end_node: Node,
    };

    fn hasPathAux(self: @This(), from: Node, word: []const Symbol, res: *std.AutoArrayHashMap(PathResult, void)) !void {
        if (word.len == 0) {
            try res.put(PathResult{
                .end_node = from,
            }, {});
            return;
        }

        exact_symbols: {
            const edge_list = self.edges_by_head.get(EdgeHead{
                .from = from,
                .symbol = word[0],
            }) orelse break :exact_symbols;
            for (edge_list.keys()) |edge| {
                try self.hasPathAux(edge.to, word[1..], res);
            }
        }
    }

    pub fn hasPath(self: @This(), alloc: std.mem.Allocator, from: Node, word: []const Symbol) ![]PathResult {
        var res = std.AutoArrayHashMap(PathResult, void).init(self.gpa);
        defer res.deinit();

        try self.hasPathAux(from, word, &res);
        return try alloc.dupe(PathResult, res.keys());
    }
};

pub fn translate_to_naive(
    gpa: std.mem.Allocator,
    arena: std.mem.Allocator,
    proc: *SM_PDS_Processor,
    unprocessed_conf: parser.ParsedSMPDS,
) !parser.ParsedSMPDS {
    var rules = std.ArrayList(parser.Rule){};
    defer rules.deinit(gpa);

    const init_phase_name = try proc.process_phase(unprocessed_conf.init.phase);

    var res_init_phase = std.ArrayList([]const u8){};
    defer res_init_phase.deinit(gpa);

    for (proc.phases.keys()) |phase_name| {
        const phase = proc.phase_names.phase_values.get(phase_name).?;
        rule_loop: for (unprocessed_conf.smpds.rules) |rule| {
            const r_name = proc.rule_names.rule_map.get(rule.name).?;
            if (phase.items.contains(r_name)) {
                switch (rule.typ) {
                    .sm => {
                        const old_phase = try proc.process_phase(rule.sm_l.?);
                        const new_phase = try proc.process_phase(rule.sm_r.?);
                        const res_phase = proc.phase_combiner.get(.{
                            .original_phase = phase_name,
                            .to_add = new_phase,
                            .to_remove = old_phase,
                        }) orelse continue :rule_loop;

                        for (unprocessed_conf.smpds.alphabet) |top| {
                            const lab = try std.fmt.allocPrint(arena, "{}", .{rules.items.len});
                            const new_rule = parser.Rule{
                                .from = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.from, phase_name }),
                                .to = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.to, res_phase }),
                                .name = lab,
                                .top = top,
                                .new_top = top,
                                .typ = .internal,
                            };
                            try rules.append(gpa, new_rule);
                            try res_init_phase.append(gpa, lab);
                        }
                    },
                    .call, .internal, .ret => {
                        const lab = try std.fmt.allocPrint(arena, "{}", .{rules.items.len});
                        const new_rule = parser.Rule{
                            .from = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.from, phase_name }),
                            .to = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.to, phase_name }),
                            .name = lab,
                            .top = rule.top.?,
                            .new_top = rule.new_top,
                            .new_tail = rule.new_tail,
                            .typ = rule.typ,
                        };
                        try rules.append(gpa, new_rule);
                        try res_init_phase.append(gpa, lab);
                    },
                }
            }
        }
    }

    const init_conf = parser.Conf{
        .state = try std.fmt.allocPrint(arena, "{s}#{}", .{ unprocessed_conf.init.state, init_phase_name }),
        .phase = try arena.dupe([]const u8, res_init_phase.items),
        .stack = unprocessed_conf.init.stack,
    };

    var states = std.StringArrayHashMap(void).init(gpa);
    defer states.deinit();
    var alphabet = std.StringArrayHashMap(void).init(gpa);
    defer alphabet.deinit();

    for (rules.items) |rule| {
        try states.put(rule.from, {});
        try states.put(rule.to, {});
        if (rule.top) |sym| {
            try alphabet.put(sym, {});
        }
        if (rule.new_top) |sym| {
            try alphabet.put(sym, {});
        }
        if (rule.new_tail) |sym| {
            try alphabet.put(sym, {});
        }
    }
    const states_sorted = try arena.dupe([]const u8, states.keys());
    std.mem.sort([]const u8, states_sorted, {}, parser.lt);
    const alphabet_sorted = try arena.dupe([]const u8, alphabet.keys());
    std.mem.sort([]const u8, alphabet_sorted, {}, parser.lt);

    const smpds = parser.SM_PDS{
        .states = states_sorted,
        .alphabet = alphabet_sorted,
        .rules = try arena.dupe(parser.Rule, rules.items),
    };

    return parser.ParsedSMPDS{
        .smpds = smpds,
        .init = init_conf,
        .branchcaret = unprocessed_conf.branchcaret,
    };
}

const StatePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: State,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        try writer.print("{s}", .{self.printer.state_map.get(self.to_print).?});
    }
};

const SymbolPrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: Symbol,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        try writer.print("{s}", .{self.printer.proc.symbols.symbol_names.get(self.to_print).?});
    }
};

const RuleNamePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: RuleName,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        try writer.print("{s}", .{self.printer.rule_map.get(self.to_print).?});
    }
};

const PhasePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: PhaseName,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        const phase = self.printer.proc.phase_names.phase_values.get(self.to_print).?;
        for (phase.items.keys(), 0..) |rn, i| {
            try writer.print("{}", .{self.printer.rulename(rn)});
            if (i < phase.items.count() - 1) {
                try writer.print(", ", .{});
            }
        }
    }
};

const RulePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: LabelledRule,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        try writer.print("{f}: ", .{self.printer.rulename(self.to_print.label)});
        switch (self.to_print.rule) {
            .int => |r| {
                try writer.print("{f} {f} -int-> {f} {?f} {?f}", .{
                    self.printer.state(r.from),
                    self.printer.symbol(r.top),
                    self.printer.state(r.to),
                    if (r.new_top) |rr| self.printer.symbol(rr) else null,
                    if (r.new_tail) |rr| self.printer.symbol(rr) else null,
                });
            },
            .call => |r| {
                try writer.print("{f} {f} -call-> {f} {f} {f}", .{
                    self.printer.state(r.from),
                    self.printer.symbol(r.top),
                    self.printer.state(r.to),
                    self.printer.symbol(r.new_top),
                    self.printer.symbol(r.new_tail),
                });
            },

            .ret => |r| {
                try writer.print("{f} {f} -ret-> {f}", .{
                    self.printer.state(r.from),
                    self.printer.symbol(r.top),
                    self.printer.state(r.to),
                });
            },

            .sm => |r| {
                try writer.print("{f} -({f} / {f})-> {f}", .{
                    self.printer.state(r.from),
                    self.printer.phase(r.old_phase),
                    self.printer.phase(r.new_phase),
                    self.printer.state(r.to),
                });
            },
        }
    }
};

pub const SM_PDS_Printer = struct {
    proc: *const SM_PDS_Processor,
    state_map: std.AutoHashMap(State, []const u8),
    rule_map: std.AutoHashMap(RuleName, []const u8),

    pub fn init(gpa: std.mem.Allocator, proc: *const SM_PDS_Processor) !SM_PDS_Printer {
        var state_map = std.AutoHashMap(State, []const u8).init(gpa);
        for (proc.states.state_map.keys()) |k| {
            try state_map.put(proc.states.state_map.get(k).?, k);
        }

        var rule_map = std.AutoHashMap(RuleName, []const u8).init(gpa);
        for (proc.rule_names.rule_map.keys()) |k| {
            try rule_map.put(proc.rule_names.rule_map.get(k).?, k);
        }

        return SM_PDS_Printer{
            .proc = proc,
            .state_map = state_map,
            .rule_map = rule_map,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.state_map.deinit();
        self.rule_map.deinit();
    }

    pub fn rulename(self: *@This(), r: RuleName) RuleNamePrinter {
        return RuleNamePrinter{
            .printer = self,
            .to_print = r,
        };
    }

    pub fn state(self: *@This(), s: State) StatePrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }

    pub fn symbol(self: *@This(), s: Symbol) SymbolPrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }

    pub fn phase(self: *@This(), s: PhaseName) PhasePrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }

    pub fn rule(self: *@This(), s: LabelledRule) RulePrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }
};

const ProcessResult = struct {
    init: Conf,
    processor: SM_PDS_Processor,
    caret: BranchCaret.Formula,
};

pub fn process(
    allocator: std.mem.Allocator,
    unprocessed_conf: parser.ParsedSMPDS,
    ap_strat: APStrategy,
) !ProcessResult {
    var processor = SM_PDS_Processor.init(allocator);

    const unprocessed = unprocessed_conf.smpds;

    try processor.process(unprocessed);
    const init = try processor.getInit(unprocessed_conf.init);

    const caret = try processCaret(
        allocator,
        unprocessed_conf.caret,
        &processor.states,
        &processor.symbols,
        processor.system.?.end_of_stack,
        ap_strat,
    );

    return ProcessResult{
        .caret = caret,
        .init = init,
        .processor = processor,
    };
}

pub const APStrategy = enum {
    substr,
    eql,
    naive,
    naive_substr,
};

pub fn AMA(comptime S: type) type {
    return struct {
        pub const NodeName = u32;

        var node_name_offset: NodeName = 0;

        pub fn add_node(_: *@This()) NodeName {
            const name = node_name_offset;
            node_name_offset += 1;
            return name;
        }

        pub fn add_init_node(self: *@This(), init: S) !NodeName {
            const name = node_name_offset;
            try self.init_names.put(init, name);
            node_name_offset += 1;
            return name;
        }

        pub const Edge = struct {
            from: NodeName,
            to: []const NodeName,
            symbol: Symbol,
        };

        init_names: std.AutoArrayHashMap(S, NodeName),
        edges: []const Edge,
    };
}

pub const BranchCaret = struct {
    pub const At = struct {
        name: []const u8,
    };

    pub const Binary = struct {
        left: Formula,
        right: Formula,
    };

    pub const Formula = union(enum) {
        const F = @This();

        at: *const At,
        nat: *const At,
        top: void,
        bot: void,
        land: *const Binary,
        lor: *const Binary,
        arg: *const Binary,
        ara: *const Binary,
        arc: *const Binary,
        erg: *const Binary,
        era: *const Binary,
        erc: *const Binary,
        aug: *const Binary,
        aua: *const Binary,
        auc: *const Binary,
        eug: *const Binary,
        eua: *const Binary,
        euc: *const Binary,
        axg: *const Formula,
        axa: *const Formula,
        axc: *const Formula,
        exg: *const Formula,
        exa: *const Formula,
        exc: *const Formula,

        pub const ArrayMapContext = struct {
            pub const prime = 1610612741;

            pub fn eql(self: @This(), left: F, right: F, i: usize) bool {
                switch (left) {
                    .at => |a| {
                        return right == .at and std.mem.eql(u8, a.name, right.at.name);
                    },
                    .nat => |a| {
                        return right == .nat and std.mem.eql(u8, a.name, right.nat.name);
                    },
                    .bot, .top => {
                        return @intFromEnum(left) == @intFromEnum(right);
                    },
                    .lor => |n| {
                        return right == .lor and self.eql(n.left, right.lor.left, i) and self.eql(n.right, right.lor.right, i);
                    },
                    .land => |n| {
                        return right == .land and self.eql(n.left, right.land.left, i) and self.eql(n.right, right.land.right, i);
                    },
                    .arg => |n| {
                        return right == .arg and self.eql(n.left, right.arg.left, i) and self.eql(n.right, right.arg.right, i);
                    },
                    .ara => |n| {
                        return right == .ara and self.eql(n.left, right.ara.left, i) and self.eql(n.right, right.ara.right, i);
                    },
                    .arc => |n| {
                        return right == .arc and self.eql(n.left, right.arc.left, i) and self.eql(n.right, right.arc.right, i);
                    },
                    .erg => |n| {
                        return right == .erg and self.eql(n.left, right.erg.left, i) and self.eql(n.right, right.erg.right, i);
                    },
                    .era => |n| {
                        return right == .era and self.eql(n.left, right.era.left, i) and self.eql(n.right, right.era.right, i);
                    },
                    .erc => |n| {
                        return right == .erc and self.eql(n.left, right.erc.left, i) and self.eql(n.right, right.erc.right, i);
                    },
                    .aug => |n| {
                        return right == .aug and self.eql(n.left, right.aug.left, i) and self.eql(n.right, right.aug.right, i);
                    },
                    .aua => |n| {
                        return right == .aua and self.eql(n.left, right.aua.left, i) and self.eql(n.right, right.aua.right, i);
                    },
                    .auc => |n| {
                        return right == .auc and self.eql(n.left, right.auc.left, i) and self.eql(n.right, right.auc.right, i);
                    },
                    .eug => |n| {
                        return right == .eug and self.eql(n.left, right.eug.left, i) and self.eql(n.right, right.eug.right, i);
                    },
                    .eua => |n| {
                        return right == .eua and self.eql(n.left, right.eua.left, i) and self.eql(n.right, right.eua.right, i);
                    },
                    .euc => |n| {
                        return right == .euc and self.eql(n.left, right.euc.left, i) and self.eql(n.right, right.euc.right, i);
                    },
                    .axg => |n| {
                        return right == .axg and self.eql(n.*, right.axg.*, i);
                    },
                    .axa => |n| {
                        return right == .axa and self.eql(n.*, right.axa.*, i);
                    },
                    .axc => |n| {
                        return right == .axc and self.eql(n.*, right.axc.*, i);
                    },
                    .exg => |n| {
                        return right == .exg and self.eql(n.*, right.exg.*, i);
                    },
                    .exa => |n| {
                        return right == .exa and self.eql(n.*, right.exa.*, i);
                    },
                    .exc => |n| {
                        return right == .exc and self.eql(n.*, right.exc.*, i);
                    },
                }
            }

            fn hashAux(self: @This(), f: F, depth: u32) u32 {
                return depth *% blk: switch (f) {
                    .bot, .top => @intFromEnum(f),
                    .at => |a| {
                        const str_hash: u32 = @truncate(std.hash_map.hashString(a.name));
                        break :blk @intFromEnum(f) *% (str_hash *% prime);
                    },
                    .nat => |a| {
                        const str_hash: u32 = @truncate(std.hash_map.hashString(a.name));
                        break :blk @intFromEnum(f) *% (str_hash *% prime);
                    },
                    .lor => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .land => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .arg => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .ara => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .arc => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .erg => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .era => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .erc => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .aug => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .aua => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .auc => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .eug => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .eua => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .euc => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .axg => |n| @intFromEnum(f) *% self.hashAux(n.*, depth *% prime),
                    .axa => |n| @intFromEnum(f) *% self.hashAux(n.*, depth *% prime),
                    .axc => |n| @intFromEnum(f) *% self.hashAux(n.*, depth *% prime),
                    .exg => |n| @intFromEnum(f) *% self.hashAux(n.*, depth *% prime),
                    .exa => |n| @intFromEnum(f) *% self.hashAux(n.*, depth *% prime),
                    .exc => |n| @intFromEnum(f) *% self.hashAux(n.*, depth *% prime),
                };
            }

            pub fn hash(self: @This(), f: F) u32 {
                return self.hashAux(f, prime);
            }
        };

        pub fn format(
            self: @This(),
            writer: anytype,
        ) !void {
            return switch (self) {
                .at => |at| try writer.print("{s}", .{at.name}),
                .nat => |at| try writer.print("!{s}", .{at.name}),
                .top => try writer.print("True", .{}),
                .bot => try writer.print("False", .{}),
                .land => |node| try writer.print("({f} && {f})", .{ node.left, node.right }),
                .lor => |node| try writer.print("({f} || {f})", .{ node.left, node.right }),
                .arg => |node| try writer.print("A[{f} Rg {f}]", .{ node.left, node.right }),
                .ara => |node| try writer.print("A[{f} Ra {f}]", .{ node.left, node.right }),
                .arc => |node| try writer.print("A[{f} Rc {f}]", .{ node.left, node.right }),
                .erg => |node| try writer.print("E[{f} Rg {f}]", .{ node.left, node.right }),
                .era => |node| try writer.print("E[{f} Ra {f}]", .{ node.left, node.right }),
                .erc => |node| try writer.print("E[{f} Rc {f}]", .{ node.left, node.right }),
                .aug => |node| try writer.print("A[{f} Ug {f}]", .{ node.left, node.right }),
                .aua => |node| try writer.print("A[{f} Ua {f}]", .{ node.left, node.right }),
                .auc => |node| try writer.print("A[{f} Uc {f}]", .{ node.left, node.right }),
                .eug => |node| try writer.print("E[{f} Ug {f}]", .{ node.left, node.right }),
                .eua => |node| try writer.print("E[{f} Ua {f}]", .{ node.left, node.right }),
                .euc => |node| try writer.print("E[{f} Uc {f}]", .{ node.left, node.right }),
                .axg => |node| try writer.print("(AXg {f})", .{node}),
                .axa => |node| try writer.print("(AXa {f})", .{node}),
                .axc => |node| try writer.print("(AXc {f})", .{node}),
                .exg => |node| try writer.print("(EXg {f})", .{node}),
                .exa => |node| try writer.print("(EXa {f})", .{node}),
                .exc => |node| try writer.print("(EXc {f})", .{node}),
            };
        }

        fn cloneBin(alloc: std.mem.Allocator, comptime op: []const u8, n: *const Binary) !Formula {
            const new_node = try alloc.create(Binary);
            new_node.* = .{ .left = try n.left.clone(alloc), .right = try n.right.clone(alloc) };
            return @unionInit(Formula, op, new_node);
        }
        fn cloneUn(alloc: std.mem.Allocator, comptime op: []const u8, n: *const Formula) !Formula {
            const new_node = try alloc.create(Formula);
            new_node.* = try n.clone(alloc);
            return @unionInit(Formula, op, new_node);
        }

        pub fn clone(self: @This(), alloc: std.mem.Allocator) error{OutOfMemory}!Formula {
            return switch (self) {
                .bot, .top, .at, .nat => self,
                .lor => |n| cloneBin(alloc, "lor", n),
                .land => |n| cloneBin(alloc, "land", n),
                .arg => |n| cloneBin(alloc, "arg", n),
                .ara => |n| cloneBin(alloc, "ara", n),
                .arc => |n| cloneBin(alloc, "arc", n),
                .erg => |n| cloneBin(alloc, "erg", n),
                .era => |n| cloneBin(alloc, "era", n),
                .erc => |n| cloneBin(alloc, "erc", n),
                .aug => |n| cloneBin(alloc, "aug", n),
                .aua => |n| cloneBin(alloc, "aua", n),
                .auc => |n| cloneBin(alloc, "auc", n),
                .eug => |n| cloneBin(alloc, "eug", n),
                .eua => |n| cloneBin(alloc, "eua", n),
                .euc => |n| cloneBin(alloc, "euc", n),
                .axg => |n| cloneUn(alloc, "axg", n),
                .axa => |n| cloneUn(alloc, "axa", n),
                .axc => |n| cloneUn(alloc, "axc", n),
                .exg => |n| cloneUn(alloc, "exg", n),
                .exa => |n| cloneUn(alloc, "exa", n),
                .exc => |n| cloneUn(alloc, "exc", n),
            };
        }

        fn deinitBin(alloc: std.mem.Allocator, n: *const Binary) void {
            n.left.deinit(alloc);
            n.right.deinit(alloc);
            alloc.destroy(n);
        }

        fn deinitUn(alloc: std.mem.Allocator, n: *const Formula) void {
            n.deinit(alloc);
            alloc.destroy(n);
        }

        pub fn deinit(self: @This(), alloc: std.mem.Allocator) void {
            switch (self) {
                .bot, .top, .at, .nat => return,
                .lor => |n| deinitBin(alloc, n),
                .land => |n| deinitBin(alloc, n),
                .arg => |n| deinitBin(alloc, n),
                .ara => |n| deinitBin(alloc, n),
                .arc => |n| deinitBin(alloc, n),
                .erg => |n| deinitBin(alloc, n),
                .era => |n| deinitBin(alloc, n),
                .erc => |n| deinitBin(alloc, n),
                .aug => |n| deinitBin(alloc, n),
                .aua => |n| deinitBin(alloc, n),
                .auc => |n| deinitBin(alloc, n),
                .eug => |n| deinitBin(alloc, n),
                .eua => |n| deinitBin(alloc, n),
                .euc => |n| deinitBin(alloc, n),
                .axg => |n| deinitUn(alloc, n),
                .axa => |n| deinitUn(alloc, n),
                .axc => |n| deinitUn(alloc, n),
                .exg => |n| deinitUn(alloc, n),
                .exa => |n| deinitUn(alloc, n),
                .exc => |n| deinitUn(alloc, n),
            }
        }

        pub fn getClosureAux(
            gpa: std.mem.Allocator,
            formula: Formula,
            closure: *std.ArrayList(Formula),
            visited: *std.ArrayHashMap(Formula, void, ArrayMapContext, false),
        ) !void {
            if (visited.contains(formula)) {
                return;
            }
            try visited.put(formula, {});

            switch (formula) {
                .top, .bot, .at, .nat => {
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .lor, .land => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .arg => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .ara => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .arc => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .erg => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .era => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .erc => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .aug => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .aua => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .auc => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .eug => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .eua => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .euc => |node| {
                    try getClosureAux(gpa, node.left, closure, visited);
                    try getClosureAux(gpa, node.right, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .axg => |node| {
                    try getClosureAux(gpa, node.*, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .axa => |node| {
                    try getClosureAux(gpa, node.*, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .axc => |node| {
                    try getClosureAux(gpa, node.*, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .exg => |node| {
                    try getClosureAux(gpa, node.*, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .exa => |node| {
                    try getClosureAux(gpa, node.*, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
                .exc => |node| {
                    try getClosureAux(gpa, node.*, closure, visited);
                    try closure.append(gpa, try formula.clone(gpa));
                },
            }
        }

        pub fn get_closure(self: @This(), gpa: std.mem.Allocator) ![]const Formula {
            var closure = std.ArrayList(Formula){};
            defer closure.deinit(gpa);

            var visited = std.ArrayHashMap(Formula, void, ArrayMapContext, false).init(gpa);
            defer {
                visited.deinit();
            }

            try getClosureAux(gpa, self, &closure, &visited);

            return try closure.toOwnedSlice(gpa);
        }

        pub fn hasAP(self: @This(), ap: []const u8) bool {
            return switch (self) {
                .at => |a| std.mem.eql(u8, ap, a.name),
                .nat => |a| std.mem.eql(u8, ap, a.name),
                .lor => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .land => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .arg => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .ara => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .arc => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .erg => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .era => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .erc => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .aug => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .aua => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .auc => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .eug => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .eua => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .euc => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .axg => |s| s.hasAP(ap),
                .axa => |s| s.hasAP(ap),
                .axc => |s| s.hasAP(ap),
                .exg => |s| s.hasAP(ap),
                .exa => |s| s.hasAP(ap),
                .exc => |s| s.hasAP(ap),
                else => false,
            };
        }
    };
};

pub fn processCaretAux(allocator: std.mem.Allocator, bcaret_raw: *const Unprocessed.RawBranchCaret) !BranchCaret.Formula {
    switch (bcaret_raw.*) {
        .ap => |node| {
            const at = try allocator.create(BranchCaret.At);
            at.* = BranchCaret.At{
                .name = try allocator.dupe(u8, node),
            };

            return BranchCaret.Formula{ .at = at };
        },
        .not_ap => |node| {
            const at = try allocator.create(BranchCaret.At);
            at.* = BranchCaret.At{
                .name = try allocator.dupe(u8, node),
            };

            return BranchCaret.Formula{ .nat = at };
        },
        .top => return .top,
        .bot => return .bot,
        .lor => |raw_node| {
            const node = try allocator.create(BranchCaret.Binary);
            node.* = .{
                .left = try processCaretAux(allocator, raw_node.left),
                .right = try processCaretAux(allocator, raw_node.right),
            };
            return BranchCaret.Formula{ .lor = node };
        },
        .land => |raw_node| {
            const node = try allocator.create(BranchCaret.Binary);
            node.* = .{
                .left = try processCaretAux(allocator, raw_node.left),
                .right = try processCaretAux(allocator, raw_node.right),
            };
            return BranchCaret.Formula{ .land = node };
        },
        .A => |raw_modal_node| {
            switch (raw_modal_node.*) {
                .U => |raw_u_node| {
                    const node = try allocator.create(BranchCaret.Binary);
                    node.* = .{
                        .left = try processCaretAux(allocator, raw_u_node.left),
                        .right = try processCaretAux(allocator, raw_u_node.right),
                    };
                    switch (raw_u_node.mode) {
                        .g => return BranchCaret.Formula{ .aug = node },
                        .a => return BranchCaret.Formula{ .aua = node },
                        .c => return BranchCaret.Formula{ .auc = node },
                    }
                },
                .R => |raw_u_node| {
                    const node = try allocator.create(BranchCaret.Binary);
                    node.* = .{
                        .left = try processCaretAux(allocator, raw_u_node.left),
                        .right = try processCaretAux(allocator, raw_u_node.right),
                    };
                    switch (raw_u_node.mode) {
                        .g => return BranchCaret.Formula{ .arg = node },
                        .a => return BranchCaret.Formula{ .ara = node },
                        .c => return BranchCaret.Formula{ .arc = node },
                    }
                },
                .X => |raw_x_node| {
                    const node = try allocator.create(BranchCaret.Formula);
                    node.* = try processCaretAux(allocator, raw_x_node.next);
                    switch (raw_x_node.mode) {
                        .g => return BranchCaret.Formula{ .axg = node },
                        .a => return BranchCaret.Formula{ .axa = node },
                        .c => return BranchCaret.Formula{ .axc = node },
                    }
                },
                else => unreachable,
            }
        },
        .E => |raw_modal_node| {
            switch (raw_modal_node.*) {
                .U => |raw_u_node| {
                    const node = try allocator.create(BranchCaret.Binary);
                    node.* = .{
                        .left = try processCaretAux(allocator, raw_u_node.left),
                        .right = try processCaretAux(allocator, raw_u_node.right),
                    };
                    switch (raw_u_node.mode) {
                        .g => return BranchCaret.Formula{ .eug = node },
                        .a => return BranchCaret.Formula{ .eua = node },
                        .c => return BranchCaret.Formula{ .euc = node },
                    }
                },
                .R => |raw_u_node| {
                    const node = try allocator.create(BranchCaret.Binary);
                    node.* = .{
                        .left = try processCaretAux(allocator, raw_u_node.left),
                        .right = try processCaretAux(allocator, raw_u_node.right),
                    };
                    switch (raw_u_node.mode) {
                        .g => return BranchCaret.Formula{ .erg = node },
                        .a => return BranchCaret.Formula{ .era = node },
                        .c => return BranchCaret.Formula{ .erc = node },
                    }
                },
                .X => |raw_x_node| {
                    const node = try allocator.create(BranchCaret.Formula);
                    node.* = try processCaretAux(allocator, raw_x_node.next);
                    switch (raw_x_node.mode) {
                        .g => return BranchCaret.Formula{ .exg = node },
                        .a => return BranchCaret.Formula{ .exa = node },
                        .c => return BranchCaret.Formula{ .exc = node },
                    }
                },
                else => unreachable,
            }
        },
        else => unreachable,
    }
}

pub fn processCaret(
    arena: std.mem.Allocator,
    caret_raw: *const Unprocessed.RawBranchCaret,
) !BranchCaret.Formula {
    return processCaretAux(arena, caret_raw);
}

pub const DFA = struct {
    var offset: usize = 0;
    pub const Node = u32;
    pub const Edge = struct {
        from: Node,
        sym: []const u8,
        to: Node,
    };

    start: Node,
    finish: std.array_list.Managed(Node),
    edges: std.array_list.Managed(Edge),

    pub fn getOffset() usize {
        return offset;
    }

    pub fn deinit(self: *@This()) void {
        self.finish.deinit();
        self.edges.deinit();
    }

    pub fn add_node(_: *@This()) Node {
        const res = offset;
        offset += 1;
        return res;
    }
};

pub const NFA = struct {
    var offset: u32 = 0;
    pub const Node = u32;
    pub const Edge = struct {
        from: Node,
        sym: *const parser.Regex,
        to: Node,
    };

    max_node: Node,
    start: Node,
    finish: Node,
    edges: std.array_list.Managed(Edge),

    pub fn initFromRegex(gpa: std.mem.Allocator, regex: *const parser.Regex) !NFA {
        var nfa = NFA{
            .max_node = offset,
            .start = 0,
            .finish = 0,
            .edges = std.array_list.Managed(Edge).init(gpa),
        };
        const node1 = nfa.add_node();
        const node2 = nfa.add_node();
        nfa.start = node1;
        nfa.finish = node2;
        try nfa.edges.append(Edge{
            .from = node1,
            .sym = regex,
            .to = node2,
        });
        return nfa;
    }

    pub fn deinit(self: *@This()) void {
        self.edges.deinit();
    }

    pub fn add_node(self: *@This()) Node {
        const res = offset;
        self.max_node = offset;
        offset += 1;
        return res;
    }

    pub fn regToNfaStep(self: *@This()) !bool {
        var edge_opt: ?Edge = null;
        for (self.edges.items, 0..) |e, i| {
            switch (e.sym.*) {
                .u, .c, .star => {
                    edge_opt = e;
                    _ = self.edges.swapRemove(i);
                    break;
                },
                else => {},
            }
        }
        if (edge_opt == null) return false;
        const edge = edge_opt.?;
        switch (edge.sym.*) {
            .u => |pair| {
                try self.edges.append(Edge{
                    .from = edge.from,
                    .to = edge.to,
                    .sym = pair.left,
                });
                try self.edges.append(Edge{
                    .from = edge.from,
                    .to = edge.to,
                    .sym = pair.right,
                });
            },
            .c => |pair| {
                const new_node = self.add_node();
                try self.edges.append(Edge{
                    .from = edge.from,
                    .to = new_node,
                    .sym = pair.left,
                });
                try self.edges.append(Edge{
                    .from = new_node,
                    .to = edge.to,
                    .sym = pair.right,
                });
            },
            .star => |reg| {
                var count_left: u32 = 0;
                var count_right: u32 = 0;
                for (self.edges.items) |e| {
                    if (e.from == edge.from) {
                        count_left += 1;
                    }
                    if (e.to == edge.to) {
                        count_right += 1;
                    }
                }
                if (count_left == 0) {
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = edge.from,
                        .sym = reg,
                    });
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = edge.to,
                        .sym = &parser.epsilon,
                    });
                } else if (count_right == 0) {
                    try self.edges.append(Edge{
                        .from = edge.to,
                        .to = edge.to,
                        .sym = reg,
                    });
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = edge.to,
                        .sym = &parser.epsilon,
                    });
                } else {
                    const new_node = self.add_node();
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = new_node,
                        .sym = &parser.epsilon,
                    });
                    try self.edges.append(Edge{
                        .from = new_node,
                        .to = edge.to,
                        .sym = &parser.epsilon,
                    });
                    try self.edges.append(Edge{
                        .from = new_node,
                        .to = new_node,
                        .sym = reg,
                    });
                }
            },
            else => unreachable,
        }
        return true;
    }

    pub fn regToNfa(self: *@This()) !void {
        while (try self.regToNfaStep()) {}
    }

    fn hasPathAux(self: @This(), gpa: std.mem.Allocator, from: Node, word: []const []const u8, res: *std.AutoArrayHashMap(Node, void), epsilon_visited: *std.AutoArrayHashMap(Node, void)) !void {
        try epsilon_visited.put(from, {});
        // std.debug.print("Visited {} / ", .{from});
        // for (word) |w| {
        //     std.debug.print("{s} ", .{w});
        // }
        // std.debug.print("\n", .{});

        for (self.edges.items) |edge| {
            if (edge.from == from and !epsilon_visited.contains(edge.to)) {
                switch (edge.sym.*) {
                    .epsilon => {
                        try self.hasPathAux(gpa, edge.to, word, res, epsilon_visited);
                    },
                    else => {},
                }
            }
        }

        if (word.len == 0) {
            try res.put(from, {});
            return;
        }

        for (self.edges.items) |edge| {
            if (edge.from == from) {
                switch (edge.sym.*) {
                    .symbol => |sym| {
                        if (std.mem.eql(u8, sym, word[0])) {
                            var eps_new = std.AutoArrayHashMap(Node, void).init(gpa);
                            defer eps_new.deinit();

                            try self.hasPathAux(gpa, edge.to, word[1..], res, &eps_new);
                        }
                    },
                    .anysymbol => {
                        var eps_new = std.AutoArrayHashMap(Node, void).init(gpa);
                        defer eps_new.deinit();

                        try self.hasPathAux(gpa, edge.to, word[1..], res, &eps_new);
                    },
                    .epsilon => {},
                    else => unreachable,
                }
            }
        }
    }

    pub fn hasPath(self: @This(), gpa: std.mem.Allocator, from: Node, word: []const []const u8) !std.AutoArrayHashMap(Node, void) {
        var res = std.AutoArrayHashMap(Node, void).init(gpa);

        var eps_new = std.AutoArrayHashMap(Node, void).init(gpa);
        defer eps_new.deinit();

        try self.hasPathAux(gpa, from, word, &res, &eps_new);

        return res;
    }

    pub fn reverse(self: *@This()) void {
        for (self.edges.items) |*edge| {
            const tmp = edge.*.from;
            edge.*.from = edge.*.to;
            edge.*.to = tmp;
        }
        const tmp = self.start;
        self.start = self.finish;
        self.finish = tmp;
    }

    pub fn determinize(self: *@This(), gpa: std.mem.Allocator, alphabet: []const []const u8) !DFA {
        const TransitionRow = std.StringArrayHashMap(Node);

        var node_unions = std.ArrayHashMap(Set(Node), Node, SetContext(Node), false).init(gpa);
        defer {
            for (node_unions.keys()) |*k| {
                k.items.deinit();
            }
            node_unions.deinit();
        }

        var node_unions2 = std.AutoArrayHashMap(Node, Set(Node)).init(gpa);
        defer node_unions2.deinit();

        var transition_table = std.AutoArrayHashMap(Node, TransitionRow).init(gpa);
        defer {
            for (transition_table.keys()) |k| {
                transition_table.getPtr(k).?.deinit();
            }
            transition_table.deinit();
        }

        var visited_nodes = Set(Node){ .items = std.AutoArrayHashMap(Node, void).init(gpa) };
        defer visited_nodes.items.deinit();

        var stack = std.ArrayList(Node){};
        defer stack.deinit(gpa);

        var start_eps = try self.hasPath(gpa, self.start, &.{});
        var new_start = self.start;
        if (start_eps.count() == 1) {
            try stack.append(gpa, self.start);
            start_eps.deinit();
        } else if (start_eps.count() > 1) {
            const to_set_s = Set(Node){
                .items = start_eps,
            };
            const gop = try node_unions.getOrPut(to_set_s);
            if (gop.found_existing) {
                unreachable;
            } else {
                const new_node = self.add_node();
                gop.value_ptr.* = new_node;

                try node_unions2.put(new_node, to_set_s);
                try stack.append(gpa, new_node);
                new_start = new_node;
            }
        } else {
            unreachable;
        }
        var i: u32 = 0;
        const trap = self.add_node();
        while (stack.pop()) |cur| {
            if (visited_nodes.items.contains(cur)) {
                continue;
            }
            try visited_nodes.items.put(cur, {});

            // if (i > 12) break;
            i += 1;

            // std.debug.print("Node: {}", .{cur});
            // if (node_unions2.get(cur)) |cc| {
            //     std.debug.print("-> {{", .{});
            //     for (cc.items.keys()) |k| {
            //         std.debug.print("{}, ", .{k});
            //     }
            //     std.debug.print("}}", .{});
            // }
            // std.debug.print("\n", .{});

            var cur_set = std.ArrayList(Node){};
            defer cur_set.deinit(gpa);
            if (node_unions2.contains(cur)) {
                try cur_set.appendSlice(gpa, node_unions2.get(cur).?.items.keys());
            } else {
                try cur_set.append(gpa, cur);
            }

            var row = TransitionRow.init(gpa);

            for (alphabet) |sym| {
                var to_set = std.AutoArrayHashMap(Node, void).init(gpa);
                defer to_set.deinit();

                for (cur_set.items) |cc| {
                    // std.debug.print("Try {} / {s}:\n", .{ cc, sym });
                    var path = try self.hasPath(gpa, cc, &.{sym});
                    defer path.deinit();

                    for (path.keys()) |k| {
                        try to_set.put(k, {});
                    }
                }

                var next_node: Node = undefined;
                if (to_set.count() == 1) {
                    next_node = to_set.pop().?.key;
                } else if (to_set.count() > 1) {
                    var to_set_s = Set(Node){
                        .items = try to_set.clone(),
                    };
                    const gop = try node_unions.getOrPut(to_set_s);
                    if (gop.found_existing) {
                        next_node = gop.value_ptr.*;
                        to_set_s.items.deinit();
                    } else {
                        const new_node = self.add_node();
                        next_node = new_node;
                        gop.value_ptr.* = new_node;

                        try node_unions2.put(new_node, to_set_s);
                    }
                } else {
                    next_node = trap;
                }

                try row.put(sym, next_node);

                if (!visited_nodes.items.contains(next_node)) {
                    try stack.append(gpa, next_node);
                }
            }

            try transition_table.put(cur, row);
        }

        // for (node_unions2.keys()) |k| {
        //     std.debug.print("{} -> {{", .{k});
        //     for (node_unions2.get(k).?.items.keys()) |kk| {
        //         std.debug.print("{}, ", .{kk});
        //     }
        //     std.debug.print("}}\n", .{});
        // }

        var dfa = DFA{
            .start = new_start,
            .finish = std.array_list.Managed(DFA.Node).init(gpa),
            .edges = std.array_list.Managed(DFA.Edge).init(gpa),
        };

        for (transition_table.keys()) |from| {
            for (transition_table.get(from).?.keys()) |sym| {
                try dfa.edges.append(DFA.Edge{
                    .from = from,
                    .sym = sym,
                    .to = transition_table.get(from).?.get(sym).?,
                });
            }
        }

        for (visited_nodes.items.keys()) |node| {
            if (node_unions2.get(node)) |n_set| {
                if (n_set.items.contains(self.finish)) {
                    try dfa.finish.append(node);
                }
            }
        }
        return dfa;
    }
};

test "regex to nfa" {
    const gpa = std.testing.allocator;

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const Regex = parser.Regex;

    // gamma1 + gamma2* + (gamma1 | gamma2)* + .*
    const regex = Regex{
        .c = .{
            .left = &Regex{
                .symbol = "gamma1",
            },
            .right = &Regex{
                .c = .{
                    .left = &Regex{
                        .star = &Regex{
                            .symbol = "gamma2",
                        },
                    },
                    .right = &Regex{
                        .c = .{
                            .left = &Regex{
                                .star = &Regex{
                                    .u = .{ .left = &Regex{
                                        .symbol = "gamma1",
                                    }, .right = &Regex{
                                        .symbol = "gamma2",
                                    } },
                                },
                            },
                            .right = &Regex{
                                .star = &Regex{
                                    .anysymbol = {},
                                },
                            },
                        },
                    },
                },
            },
        },
    };

    var nfa = try NFA.initFromRegex(gpa, &regex);
    defer nfa.deinit();

    try nfa.regToNfa();
    nfa.reverse();

    // for (nfa.edges.items) |e| {
    //     std.debug.print("{} - {} -> {}\n", .{ e.from, e.sym.*, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {}\n", .{ nfa.start, nfa.finish });

    var dfa = try nfa.determinize(gpa, &.{ "gamma1", "gamma2" });
    defer dfa.deinit();

    // for (dfa.edges.items) |e| {
    //     std.debug.print("{} - {s} -> {}\n", .{ e.from, e.sym, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {any}\n", .{ dfa.start, dfa.finish.items });
}

test "regex to nfa 2" {
    const gpa = std.testing.allocator;

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const Regex = parser.Regex;

    // . + gamma2 + .*
    const regex = Regex{
        .c = .{
            .left = &Regex{
                .anysymbol = {},
            },
            .right = &Regex{
                .c = .{
                    .left = &Regex{
                        .symbol = "gamma2",
                    },
                    .right = &Regex{
                        .star = &Regex{
                            .anysymbol = {},
                        },
                    },
                },
            },
        },
    };

    var nfa = try NFA.initFromRegex(gpa, &regex);
    defer nfa.deinit();

    try nfa.regToNfa();
    nfa.reverse();

    // for (nfa.edges.items) |e| {
    //     std.debug.print("{} - {} -> {}\n", .{ e.from, e.sym.*, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {}\n", .{ nfa.start, nfa.finish });

    var dfa = try nfa.determinize(gpa, &.{ "gamma1", "gamma2" });
    defer dfa.deinit();

    // for (dfa.edges.items) |e| {
    //     std.debug.print("{} - {s} -> {}\n", .{ e.from, e.sym, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {any}\n", .{ dfa.start, dfa.finish.items });
}

test "regex ap" {
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    StateProcessor.state_name_offset = 0;
    PhaseProcessor.phase_name_offset = 0;
    SymbolProcessor.symbol_name_offset = 0;
    RuleNameProcessor.rule_name_offset = 0;

    var processor = SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer processor.deinit();

    var file = parser.SmpdsFile.open(allocator, "examples/process_test_regex.smpds");
    // var file = parser.SmpdsFile.open(allocator, "tests/true-2.smpds");
    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try processor.process(unprocessed, unprocessed_conf.init);
    // var in = try processor.getInit(unprocessed_conf.init);

    const formula = try processCaret(arena.allocator(), unprocessed_conf.branchcaret.formula);

    var lambda = try LabellingFunction.init(gpa, &processor, formula, LabellingFunction.strict, unprocessed_conf.branchcaret.valuations);
    defer lambda.deinit();

    var printer = try SM_PDS_Printer.init(allocator, &processor);
    defer printer.deinit();

    // for (processor.system.?.rules.items) |lr| {
    //     std.debug.print("{}\n", .{printer.rule(lr)});
    // }

    // for (lambda.state_aps.keys()) |pair| {
    //     if (lambda.state_aps.get(pair).?.count() < 1) continue;
    //     std.debug.print("<{}, {}>: ", .{ printer.state(pair.state), printer.symbol(pair.top) });
    //     for (lambda.state_aps.get(pair).?.keys()) |ap| {
    //         std.debug.print("{s}, ", .{ap});
    //     }
    //     std.debug.print("\n", .{});
    // }

    // std.debug.print("Init: {} ", .{printer.state(in.state)});
    // for (in.stack) |sym| {
    //     std.debug.print("{}, ", .{printer.symbol(sym)});
    // }
    // std.debug.print(" # {}\n", .{printer.phase(in.phase)});
}

// test "processing" {
//     var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
//     defer arena.deinit();
//     const allocator = arena.allocator();

//     StateProcessor.state_name_offset = 0;
//     PhaseProcessor.phase_name_offset = 0;
//     SymbolProcessor.symbol_name_offset = 0;
//     RuleNameProcessor.rule_name_offset = 0;

//     var processor = SM_PDS_Processor.init(allocator, std.testing.allocator);
//     defer processor.deinit();

//     var file = parser.SmpdsFile.open(allocator, "examples/process_test.smpds");
//     const unprocessed_conf = try file.parse();
//     const unprocessed = unprocessed_conf.smpds;
//     try processor.process(unprocessed, unprocessed_conf.init);
//     _ = try processor.getInit(unprocessed_conf.init);

//     try std.testing.expectEqual(3, processor.states.state_map.count());
//     try std.testing.expectEqual(0, processor.states.state_map.get("p1").?);
//     try std.testing.expectEqual(1, processor.states.state_map.get("p2").?);
//     try std.testing.expectEqual(2, processor.states.state_map.get("p3").?);

//     try std.testing.expectEqual(6, processor.rule_names.rule_map.count());
//     try std.testing.expectEqual(0, processor.rule_names.rule_map.get("r1").?);
//     try std.testing.expectEqual(1, processor.rule_names.rule_map.get("r2").?);
//     try std.testing.expectEqual(2, processor.rule_names.rule_map.get("r3").?);
//     try std.testing.expectEqual(3, processor.rule_names.rule_map.get("r4").?);
//     try std.testing.expectEqual(4, processor.rule_names.rule_map.get("r5").?);
//     try std.testing.expectEqual(5, processor.rule_names.rule_map.get("r6").?);

//     try std.testing.expectEqual(3, processor.symbols.symbol_map.count());
//     try std.testing.expectEqual(0, processor.symbols.symbol_map.get("g1").?);
//     try std.testing.expectEqual(1, processor.symbols.symbol_map.get("g2").?);
//     try std.testing.expectEqual(2, processor.symbols.symbol_map.get("#").?);

//     try std.testing.expectEqual(4, processor.system.?.phases.phase_values.count());
//     try std.testing.expectEqual(1, processor.system.?.phases.phase_values.get(0).?.items.count());
//     try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(0).?.items.get(0).?);
//     try std.testing.expectEqual(1, processor.system.?.phases.phase_values.get(1).?.items.count());
//     try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(1).?.items.get(2).?);
//     try std.testing.expectEqual(3, processor.system.?.phases.phase_values.get(2).?.items.count());
//     try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(2).?.items.get(0).?);
//     try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(2).?.items.get(1).?);
//     try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(2).?.items.get(2).?);
//     try std.testing.expectEqual(2, processor.system.?.phases.phase_values.get(3).?.items.count());
//     try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(3).?.items.get(1).?);
//     try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(3).?.items.get(2).?);

//     try std.testing.expectEqual(6, processor.system.?.rules.items.len);
//     try std.testing.expectEqualDeep(LabelledRule{
//         .label = 0,
//         .rule = Rule{
//             .int = InternalRule{
//                 .from = 0,
//                 .top = 0,
//                 .to = 1,
//                 .new_top = 1,
//                 .new_tail = 0,
//             },
//         },
//     }, processor.system.?.rules.items[0]);

//     try std.testing.expectEqualDeep(LabelledRule{
//         .label = 1,
//         .rule = Rule{
//             .call = CallRule{
//                 .from = 0,
//                 .top = 0,
//                 .to = 1,
//                 .new_top = 1,
//                 .new_tail = 0,
//             },
//         },
//     }, processor.system.?.rules.items[1]);

//     try std.testing.expectEqualDeep(LabelledRule{
//         .label = 2,
//         .rule = Rule{
//             .sm = SMRule{
//                 .from = 2,
//                 .to = 2,
//                 .old_phase = 0,
//                 .new_phase = 1,
//             },
//         },
//     }, processor.system.?.rules.items[2]);

//     try std.testing.expectEqualDeep(LabelledRule{
//         .label = 3,
//         .rule = Rule{
//             .int = InternalRule{
//                 .from = 2,
//                 .top = 1,
//                 .to = 2,
//                 .new_top = 1,
//                 .new_tail = null,
//             },
//         },
//     }, processor.system.?.rules.items[3]);

//     try std.testing.expectEqualDeep(LabelledRule{
//         .label = 4,
//         .rule = Rule{
//             .int = InternalRule{
//                 .from = 2,
//                 .top = 1,
//                 .to = 2,
//                 .new_top = null,
//                 .new_tail = null,
//             },
//         },
//     }, processor.system.?.rules.items[4]);

//     try std.testing.expectEqualDeep(LabelledRule{
//         .label = 5,
//         .rule = Rule{
//             .ret = RetRule{
//                 .from = 2,
//                 .top = 1,
//                 .to = 2,
//             },
//         },
//     }, processor.system.?.rules.items[5]);
// }

test "caret process" {
    {
        var alloc = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer alloc.deinit();
        const unproc = Unprocessed.RawBranchCaret{ .ap = "at" };
        const correct = BranchCaret.Formula{ .at = &BranchCaret.At{ .name = "at" } };
        try std.testing.expectEqualDeep(correct, processCaret(alloc.allocator(), &unproc));
    }
    {
        var alloc = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer alloc.deinit();
        const unproc = Unprocessed.RawBranchCaret{
            .A = &.{
                .U = .{
                    .mode = .g,
                    .left = &Unprocessed.RawBranchCaret{ .top = {} },
                    .right = &Unprocessed.RawBranchCaret{
                        .E = &.{
                            .X = .{ .mode = .a, .next = &Unprocessed.RawBranchCaret{
                                .ap = "123",
                            } },
                        },
                    },
                },
            },
        };
        const correct = BranchCaret.Formula{
            .aug = &BranchCaret.Binary{
                .left = BranchCaret.Formula{ .top = {} },
                .right = BranchCaret.Formula{
                    .exa = &BranchCaret.Formula{
                        .at = &BranchCaret.At{ .name = "123" },
                    },
                },
            },
        };
        try std.testing.expectEqualDeep(correct, processCaret(alloc.allocator(), &unproc));
    }
}

test "closure" {
    {
        const alloc = std.testing.allocator;

        const formula = BranchCaret.Formula{
            .aug = &BranchCaret.Binary{
                .left = BranchCaret.Formula{ .top = {} },
                .right = BranchCaret.Formula{
                    .exa = &BranchCaret.Formula{
                        .at = &BranchCaret.At{ .name = "123" },
                    },
                },
            },
        };

        const cl = try formula.get_closure(alloc);
        defer {
            for (cl) |f| {
                f.deinit(alloc);
            }
            alloc.free(cl);
        }

        // for (cl) |f| {
        //     std.debug.print("{}\n", .{f});
        // }
        try std.testing.expectEqual(4, cl.len);
    }
}
