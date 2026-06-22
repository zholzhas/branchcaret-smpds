const processor = @import("processor.zig");
const std = @import("std");
const root = @import("main.zig");

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

const Formula = processor.BranchCaret.Formula;

pub const ExitLabel = enum { E, A, Eacc, Aacc };

pub const StateLabel = union(enum) {
    formula: Formula,
    exit: ExitLabel,

    pub fn format(self: @This(), writer: *std.io.Writer) !void {
        switch (self) {
            .exit => |e| try writer.print("{s}", .{@tagName(e)}),
            .formula => |f| try writer.print("{f}", .{f}),
        }
    }
};

pub const State = union(enum) {
    control: ControlState,
    ama: u32,
};

pub const ControlState = struct {
    control_point: union(enum) { state: processor.State, c: void },
    label: StateLabel,
};

pub const RetSymbol = struct {
    symbol: processor.Symbol,
    formula: Formula,
};

pub const Checkpoint = struct {
    symbol: processor.Symbol,
    call_location: processor.State,
    call_top: processor.Symbol,
};

pub const Symbol = union(enum) {
    standard: processor.Symbol,
    ret: RetSymbol,
};

pub const SymbolOrCheckpoint = union(enum) {
    checkpoint: Checkpoint,
    symbol: Symbol,
};

pub const Transition = struct {
    enabler: ?processor.RuleName = null,
    to: State,
    new_top: ?Symbol,
    new_tail: ?SymbolOrCheckpoint = null,
    old_phase: ?PhaseName = null,
    new_phase: ?PhaseName = null,
};

pub const StandardRule = struct {
    from: State,
    top: Symbol,
    transitions: []Transition,
};

pub const RestoreRule = struct {
    from: State,
    top: Checkpoint,
    to: State,
    new_top: Symbol,
};
pub const DiscardRule = struct {
    from: State,
    top: Checkpoint,
    to: State,
    new_top: Symbol,
};

pub const Rule = union(enum) {
    standard: StandardRule,
    restore: RestoreRule,
    discard: DiscardRule,

    pub const HashContext = struct {
        pub fn hash(_: HashContext, v: Rule) u32 {
            var h = std.hash.Wyhash.init(0);
            std.hash.autoHashStrat(&h, v, .Deep);
            return @truncate(h.final());
        }

        pub fn eql(_: HashContext, a: Rule, b: Rule, _: usize) bool {
            switch (a) {
                .standard => |r1| {
                    if (b != .standard) return false;
                    const r2 = b.standard;
                    if (!std.meta.eql(r1.from, r2.from)) return false;
                    if (!std.meta.eql(r1.top, r2.top)) return false;
                    if (r1.transitions.len != r2.transitions.len) return false;

                    for (r1.transitions, r2.transitions) |t1, t2| {
                        if (!std.meta.eql(t1, t2)) return false;
                    }
                    return true;
                },
                .restore => |r1| {
                    if (b != .restore) return false;
                    const r2 = b.restore;
                    if (!std.meta.eql(r1.from, r2.from)) return false;
                    if (!std.meta.eql(r1.top, r2.top)) return false;
                    if (!std.meta.eql(r1.to, r2.to)) return false;
                    if (!std.meta.eql(r1.new_top, r2.new_top)) return false;

                    return true;
                },
                .discard => |r1| {
                    if (b != .discard) return false;
                    const r2 = b.discard;
                    if (!std.meta.eql(r1.from, r2.from)) return false;
                    if (!std.meta.eql(r1.top, r2.top)) return false;
                    if (!std.meta.eql(r1.to, r2.to)) return false;
                    if (!std.meta.eql(r1.new_top, r2.new_top)) return false;

                    return true;
                },
            }
        }
    };
};

pub const StateName = *const State;
pub const PhaseName = processor.PhaseName;

pub const PhasePrinter = struct {
    printer: SM_GBPDS_Printer,
    phase: processor.PhaseName,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        const keys = self.printer.proc.phase_names.phase_values.get(self.phase).?.items.keys();
        for (keys, 0..) |r, i| {
            try writer.print("{s}", .{self.printer.rule_names.get(r).?});
            if (i < keys.len - 1) try writer.print(", ", .{});
        }
    }
};

pub const StatePrinter = struct {
    printer: SM_GBPDS_Printer,
    state: State,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        switch (self.state) {
            .control => |ss| {
                switch (ss.control_point) {
                    .state => |s| {
                        try writer.print("<{s}, {f}>", .{
                            self.printer.state_names.get(s).?,
                            ss.label,
                        });
                    },
                    .c => {
                        try writer.print("<pC, {f}>", .{
                            ss.label,
                        });
                    },
                }
            },
            .ama => |s| {
                try writer.print("<{}>", .{
                    s,
                });
            },
        }
    }
};

pub const RulePrinter = struct {
    printer: SM_GBPDS_Printer,
    rule: Rule,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        switch (self.rule) {
            .standard => |rule| {
                try writer.print("{f} {f} -[", .{ self.printer.state(rule.from), self.printer.symbol(.{ .symbol = rule.top }) });
                for (rule.transitions) |trans| {
                    if (trans.enabler) |rn| {
                        try writer.print("{s}", .{self.printer.rule_names.get(rn).?});
                    } else {
                        try writer.print("null", .{});
                    }
                    if (trans.new_phase) |_| {
                        try writer.print(" / {f} / {f}", .{ self.printer.phase(trans.old_phase.?), self.printer.phase(trans.new_phase.?) });
                    }
                    try writer.print(", ", .{});
                }
                try writer.print("]-> {{", .{});
                for (rule.transitions) |trans| {
                    if (trans.new_top) |t| {
                        if (trans.new_tail) |tt| {
                            try writer.print("{f} {f} {f}, ", .{ self.printer.state(trans.to), self.printer.symbol(.{ .symbol = t }), self.printer.symbol(tt) });
                        } else {
                            try writer.print("{f} {f}, ", .{ self.printer.state(trans.to), self.printer.symbol(.{ .symbol = t }) });
                        }
                    } else {
                        try writer.print("{f}, ", .{self.printer.state(trans.to)});
                    }
                }
                try writer.print("}}", .{});
            },
            .restore => |rule| {
                try writer.print("{f} {f} -restore-> {f} {f}", .{
                    self.printer.state(rule.from),
                    self.printer.symbol(.{ .checkpoint = rule.top }),
                    self.printer.state(rule.to),
                    self.printer.symbol(.{ .symbol = rule.new_top }),
                });
            },
            .discard => |rule| {
                try writer.print("{f} {f} -discard-> {f} {f}", .{
                    self.printer.state(rule.from),
                    self.printer.symbol(.{ .checkpoint = rule.top }),
                    self.printer.state(rule.to),
                    self.printer.symbol(.{ .symbol = rule.new_top }),
                });
            },
        }
    }
};

pub const SymbolPrinter = struct {
    printer: SM_GBPDS_Printer,
    symbol: SymbolOrCheckpoint,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        switch (self.symbol) {
            .symbol => |sym| {
                switch (sym) {
                    .standard => |s| {
                        try writer.print("{s}", .{self.printer.symbol_names.get(s).?});
                    },
                    .ret => |s| {
                        try writer.print("|{s}, {f}|", .{
                            self.printer.symbol_names.get(s.symbol).?,
                            s.formula,
                        });
                    },
                }
            },
            .checkpoint => |ch| {
                try writer.print("/{s}, {s}, {s}/", .{
                    self.printer.symbol_names.get(ch.symbol).?,
                    self.printer.state_names.get(ch.call_location).?,
                    self.printer.symbol_names.get(ch.call_top).?,
                });
            },
        }
    }
};

pub const SM_GBPDS_Printer = struct {
    proc: *processor.SM_PDS_Processor,
    state_names: std.AutoHashMap(processor.State, []const u8),
    symbol_names: std.AutoHashMap(processor.Symbol, []const u8),
    rule_names: std.AutoHashMap(processor.RuleName, []const u8),

    pub fn init(gpa: std.mem.Allocator, proc: *processor.SM_PDS_Processor) !SM_GBPDS_Printer {
        var state_names = std.AutoHashMap(processor.State, []const u8).init(gpa);
        for (proc.states.state_map.keys()) |name| {
            try state_names.put(proc.states.state_map.get(name).?, name);
        }

        var symbol_names = std.AutoHashMap(processor.Symbol, []const u8).init(gpa);
        for (proc.symbols.symbol_map.keys()) |name| {
            try symbol_names.put(proc.symbols.symbol_map.get(name).?, name);
        }

        var rule_names = std.AutoHashMap(processor.RuleName, []const u8).init(gpa);
        for (proc.rule_names.rule_map.keys()) |name| {
            try rule_names.put(proc.rule_names.rule_map.get(name).?, name);
        }

        return SM_GBPDS_Printer{
            .proc = proc,
            .state_names = state_names,
            .symbol_names = symbol_names,
            .rule_names = rule_names,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.rule_names.deinit();
        self.state_names.deinit();
        self.symbol_names.deinit();
    }

    pub fn rule(self: @This(), r: Rule) RulePrinter {
        return RulePrinter{
            .printer = self,
            .rule = r,
        };
    }

    pub fn symbol(self: @This(), s: SymbolOrCheckpoint) SymbolPrinter {
        return SymbolPrinter{
            .printer = self,
            .symbol = s,
        };
    }

    pub fn phase(self: @This(), p: PhaseName) PhasePrinter {
        return PhasePrinter{
            .printer = self,
            .phase = p,
        };
    }

    pub fn state(self: @This(), s: State) StatePrinter {
        return StatePrinter{
            .printer = self,
            .state = s,
        };
    }
};

pub const EmCheckpoint = struct {
    checkpoint: Checkpoint,
};

pub const SM_GBPDS_Processor = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    // states: std.SinglyLinkedList(State),
    state_names: std.AutoArrayHashMap(State, void),

    // symbols: std.SinglyLinkedList(Symbol),
    // symbol_names: std.AutoArrayHashMap(Symbol, SymbolName),

    rule_set: std.ArrayHashMap(Rule, void, Rule.HashContext, true),
    rule_array: std.ArrayList(Rule),

    sm_pds_proc: ?*processor.SM_PDS_Processor,
    pushed_ret_symbols: std.AutoArrayHashMap(RetSymbol, void),
    pushed_checkpoints: std.AutoArrayHashMap(EmCheckpoint, void),

    pub const AcceptType = enum { any, unexit };

    pub fn init(gpa: std.mem.Allocator, arena: std.mem.Allocator) SM_GBPDS_Processor {
        return SM_GBPDS_Processor{
            .arena = arena,
            .gpa = gpa,

            // .states = std.SinglyLinkedList(State){},
            .state_names = std.AutoArrayHashMap(State, void).init(gpa),

            // .symbols = std.SinglyLinkedList(Symbol){},
            // .symbol_names = std.AutoArrayHashMap(Symbol, SymbolName).init(gpa),

            // .rule_set = std.AutoArrayHashMap(Rule, void).init(gpa),
            .rule_set = std.ArrayHashMap(Rule, void, Rule.HashContext, true).init(gpa),
            .rule_array = .{},
            .pushed_ret_symbols = std.AutoArrayHashMap(RetSymbol, void).init(gpa),
            .pushed_checkpoints = std.AutoArrayHashMap(EmCheckpoint, void).init(gpa),

            .sm_pds_proc = null,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.state_names.deinit();
        // self.symbol_names.deinit();
        self.rule_set.deinit();
        self.rule_array.deinit(self.gpa);
        // for (self.pushed_ret_symbols.values()) |*v| {
        //     v.deinit();
        // }
        self.pushed_ret_symbols.deinit();
        // for (self.pushed_checkpoints.values()) |*v| {
        //     v.deinit();
        // }
        self.pushed_checkpoints.deinit();
    }

    // pub fn getStateName(self: *@This(), state: State) !StateName {
    //     const gop = try self.state_names.getOrPut(state);
    //     if (gop.found_existing) {
    //         return gop.value_ptr.*;
    //     } else {
    //         const node = try self.arena.create(State);
    //         node.* = state;
    //         gop.value_ptr.* = node;
    //         return node;
    //     }
    // }
    pub fn getStateName(self: *@This(), state: State) !State {
        try self.state_names.put(state, {});
        return state;
    }

    // pub fn getSymbolName(self: *@This(), symbol: Symbol) !SymbolName {
    //     const gop = try self.symbol_names.getOrPut(symbol);
    //     if (gop.found_existing) {
    //         return gop.value_ptr.*;
    //     } else {
    //         const node = try self.arena.create(Symbol);
    //         node.* = symbol;
    //         gop.value_ptr.* = node;
    //         return node;
    //     }
    // }

    pub fn storeRuleNoCheckpoint(self: *@This(), rule: Rule) !void {
        if (self.rule_set.contains(rule)) return;
        try self.rule_set.putNoClobber(rule, {});
        try self.rule_array.append(self.gpa, rule);

        switch (rule) {
            .standard => |r| {
                for (r.transitions) |t| {
                    if (t.new_tail) |nt| {
                        switch (nt) {
                            .symbol => |s| {
                                switch (s) {
                                    .ret => |ret| {
                                        try self.pushed_ret_symbols.put(ret, {});
                                    },
                                    else => {},
                                }
                            },
                            .checkpoint => unreachable,
                        }
                    }
                }
            },
            else => {},
        }
    }
    pub fn storeRule(self: *@This(), rule: Rule) !void {
        if (self.rule_set.contains(rule)) return;
        try self.rule_set.putNoClobber(rule, {});
        try self.rule_array.append(self.gpa, rule);

        switch (rule) {
            .standard => |r| {
                for (r.transitions) |t| {
                    if (t.new_tail) |nt| {
                        switch (nt) {
                            .symbol => |s| {
                                switch (s) {
                                    .ret => |ret| {
                                        try self.pushed_ret_symbols.put(ret, {});
                                    },
                                    else => {},
                                }
                            },
                            .checkpoint => |ch| {
                                try self.pushed_checkpoints.put(.{ .checkpoint = ch }, {});
                            },
                        }
                    }
                }
            },
            else => {},
        }
    }

    fn simplifyPostStar(self: *@This(), gpa: std.mem.Allocator, ini_state: State) !void {
        var ma = PostMA{};
        defer ma.deinit(gpa);

        var node_offset: u32 = 0;

        var cur: PostMA.Node = .{ .st = .{ .state = ini_state } };
        var acc = false;
        for (self.sm_pds_proc.?.system.?.init_conf.stack, 0..) |sym, symi| {
            if (symi >= self.sm_pds_proc.?.system.?.init_conf.stack.len - 1) {
                acc = true;
            }
            _ = try ma.addEdge(gpa, .{
                .from = cur,
                .symbol = .{ .symbol = .{ .symbol = .{ .standard = sym } } },
                .to = .{ .int = .{ .id = node_offset, .accepting = acc } },
            });
            cur = .{ .int = .{ .id = node_offset, .accepting = acc } };
            node_offset += 1;
        }

        try ma.constructPostStar(gpa, self);
        var rules_to_delete = std.ArrayList(usize).empty;
        defer rules_to_delete.deinit(gpa);
        for (self.rule_array.items, 0..) |rule, ri| {
            switch (rule) {
                .standard => |r| {
                    if (r.from == .ama) continue;
                    if (!ma.edges_by_head_sym.contains(.{
                        .state = .{ .st = .{ .state = r.from } },
                        .sym = .{ .symbol = .{ .symbol = r.top } },
                    })) {
                        try rules_to_delete.append(gpa, ri);
                    }
                },
                .restore => |r| {
                    if (!ma.edges_by_head_sym.contains(.{
                        .state = .{ .st = .{ .state = r.from } },
                        .sym = .{ .symbol = .{ .checkpoint = r.top } },
                    })) {
                        try rules_to_delete.append(gpa, ri);
                    }
                },
                .discard => |r| {
                    if (!ma.edges_by_head_sym.contains(.{
                        .state = .{ .st = .{ .state = r.from } },
                        .sym = .{ .symbol = .{ .checkpoint = r.top } },
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
            _ = self.rule_array.swapRemove(ri);
        }
    }

    pub fn construct_optimized(
        self: *@This(),
        sm_pds_proc: *processor.SM_PDS_Processor,
        closure: []const Formula,
        lambda: processor.LabellingFunction,
        init_state: State,
        _: processor.PhaseName,
        pre_ma: *const processor.MA,
    ) !void {
        _ = .{ closure, pre_ma };
        const sm_pds = sm_pds_proc.system.?;

        self.sm_pds_proc = sm_pds_proc;

        var rules_by_src = std.AutoHashMap(processor.State, std.ArrayList(usize)).init(self.gpa);
        const StateTop = struct { state: processor.State, top: processor.Symbol };
        var rules_by_lhs = std.AutoHashMap(StateTop, std.ArrayList(usize)).init(self.gpa);

        defer {
            var it = rules_by_lhs.iterator();
            while (it.next()) |k| {
                k.value_ptr.deinit(self.gpa);
            }
            rules_by_lhs.deinit();
        }
        defer {
            var it = rules_by_src.iterator();
            while (it.next()) |k| {
                k.value_ptr.deinit(self.gpa);
            }
            rules_by_src.deinit();
        }

        for (sm_pds.rules.items, 0..) |lr, i| {
            const src = switch (lr.rule) {
                .int => |r| r.from,
                .call => |r| r.from,
                .ret => |r| r.from,
                .sm => |r| r.from,
            };
            const gop = try rules_by_src.getOrPut(src);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.ArrayList(usize){};
            }
            try gop.value_ptr.append(self.gpa, i);

            switch (lr.rule) {
                .int => |r| {
                    const gop2 = try rules_by_lhs.getOrPutValue(.{ .state = r.from, .top = r.top }, std.ArrayList(usize){});
                    try gop2.value_ptr.append(self.gpa, i);
                },
                .call => |r| {
                    const gop2 = try rules_by_lhs.getOrPutValue(.{ .state = r.from, .top = r.top }, std.ArrayList(usize){});
                    try gop2.value_ptr.append(self.gpa, i);
                },
                .ret => |r| {
                    const gop2 = try rules_by_lhs.getOrPutValue(.{ .state = r.from, .top = r.top }, std.ArrayList(usize){});
                    try gop2.value_ptr.append(self.gpa, i);
                },
                .sm => |r| {
                    for (sm_pds_proc.symbols.symbol_names.keys()) |gamma| {
                        const gop2 = try rules_by_lhs.getOrPutValue(.{ .state = r.from, .top = gamma }, std.ArrayList(usize){});
                        try gop2.value_ptr.append(self.gpa, i);
                    }
                },
            }
        }

        var visited_states = std.AutoArrayHashMap(struct { state: State }, void).init(self.gpa);
        defer visited_states.deinit();

        var stack = StackSet(struct { state: State }){};
        defer stack.deinit(self.gpa);

        try stack.append(self.gpa, .{ .state = init_state });

        var c_states = std.AutoArrayHashMap(State, void).init(self.gpa);
        defer c_states.deinit();

        var ret_rules = std.AutoArrayHashMap(processor.State, void).init(self.gpa);
        defer {
            ret_rules.deinit();
        }

        for (sm_pds.rules.items) |rule| {
            switch (rule.rule) {
                .ret => |r| {
                    try ret_rules.put(r.to, {});
                },
                else => {},
            }
        }

        var dfa_states = std.AutoArrayHashMap(u32, void).init(self.gpa);
        defer dfa_states.deinit();

        for (lambda.dfas.items) |dfa| {
            for (dfa.edges.items) |edge| {
                try dfa_states.put(edge.from, {});
                try dfa_states.put(edge.to, {});
            }
        }

        root.recordTime("GBPDS construction start", .{});

        var printer = try SM_GBPDS_Printer.init(self.gpa, sm_pds_proc);
        defer printer.deinit();
        while (true) {
            const num_rules = self.rule_set.count();
            stack: while (stack.pop()) |cur_pair| {
                // std.debug.print("Stack: {{ ", .{});
                // for (stack.stack.items) |it| {
                //     std.debug.print("{f}/{}, ", .{ printer.state(it.state), it.phase });
                // }
                //
                // std.debug.print("{f}/{} }}\n", .{ printer.state(cur_pair.state), cur_pair.phase });
                const cur = cur_pair.state;

                _ = try self.getStateName(cur);
                // if (stack.capacity > stack.items.len * 3) {
                //     stack.shrinkAndFree(self.gpa, stack.items.len);
                // }
                if (visited_states.contains(.{ .state = cur })) {
                    // std.debug.print("Skipping...\n", .{});
                    continue;
                }
                try visited_states.putNoClobber(.{ .state = cur }, {});
                // check early if it is pC. If yes, don't do the big switch!
                if (cur.control.control_point == .c) {
                    try c_states.put(cur, {});
                    continue;
                }
                // std.debug.print("Eval {f}/{}\n", .{ printer.state(cur), cur_phase });

                // switch on the current state label and apply rules
                switch (cur.control.label) {
                    .formula => |f| {
                        switch (f) {
                            .top => {
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {

                                    // create self loop
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{Transition{
                                            .to = cur,
                                            .new_top = .{ .standard = gamma },
                                        }}),
                                    } });
                                }
                            },
                            .bot => {},
                            .at => |a| {
                                if (lambda.state_aps.get(cur.control.control_point.state).?.contains(a.name)) {
                                    for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {

                                        // create self loop
                                        try self.storeRule(Rule{ .standard = StandardRule{
                                            .from = cur,
                                            .top = .{ .standard = gamma },
                                            .transitions = try self.arena.dupe(Transition, &.{Transition{
                                                .to = cur,
                                                .new_top = .{ .standard = gamma },
                                            }}),
                                        } });
                                    }
                                }

                                if (lambda.ap_dfas.get(a.name)) |ap_dfas| {
                                    if (ap_dfas.get(cur.control.control_point.state)) |dfa_num| {
                                        const dfa = lambda.dfas.items[dfa_num];
                                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = gamma },
                                                .transitions = try self.arena.dupe(Transition, &.{Transition{
                                                    .to = .{ .ama = dfa.start },
                                                    .new_top = .{ .standard = gamma },
                                                }}),
                                            } });
                                        }

                                        for (dfa.edges.items) |edge| {
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = .{ .ama = edge.from },
                                                .top = .{ .standard = self.sm_pds_proc.?.symbols.symbol_map.get(edge.sym).? },
                                                .transitions = try self.arena.dupe(Transition, &.{Transition{
                                                    .to = .{ .ama = edge.to },
                                                    .new_top = null,
                                                }}),
                                            } });
                                        }
                                        for (dfa.finish.items) |finish| {
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = .{ .ama = finish },
                                                .top = .{ .standard = self.sm_pds_proc.?.symbols.symbol_map.get("#").? },
                                                .transitions = try self.arena.dupe(Transition, &.{Transition{
                                                    .to = .{ .ama = finish },
                                                    .new_top = .{ .standard = self.sm_pds_proc.?.symbols.symbol_map.get("#").? },
                                                }}),
                                            } });
                                        }
                                    }
                                }
                            },
                            .nat => |a| {
                                var negated = false;
                                if (!lambda.state_aps.get(cur.control.control_point.state).?.contains(a.name) and !lambda.ap_dfas.contains(a.name)) {
                                    negated = true;
                                    for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {

                                        // create self loop
                                        // we have a problem here:
                                        // we also need to decode pushed checkpoints and return symbols somehow
                                        try self.storeRule(Rule{ .standard = StandardRule{
                                            .from = cur,
                                            .top = .{ .standard = gamma },
                                            .transitions = try self.arena.dupe(Transition, &.{Transition{
                                                .to = cur,
                                                .new_top = .{ .standard = gamma },
                                            }}),
                                        } });
                                    }
                                }
                                if (lambda.ap_dfas.get(a.name)) |ap_dfas| {
                                    if (ap_dfas.get(cur.control.control_point.state)) |_| {
                                        @panic("Negated atomic propositions with regular valuations are not implemented");
                                    } else if (!negated) {
                                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                            // create self loop
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = gamma },
                                                .transitions = try self.arena.dupe(Transition, &.{Transition{
                                                    .to = cur,
                                                    .new_top = .{ .standard = gamma },
                                                }}),
                                            } });
                                        }
                                    }
                                }
                            },
                            .land => |node| {
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                const to2 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to2,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .to = to1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .to = to2,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                            },
                            .lor => |node| {
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                const to2 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to2,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .to = to1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .to = to2,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                            },
                            .exg => |node| {
                                for ((rules_by_src.get(cur.control.control_point.state) orelse continue :stack).items) |ri| {
                                    const lrule = sm_pds.rules.items[ri];
                                    switch (lrule.rule) {
                                        .int => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = node.*,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                        .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .ret => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = node.*,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .call => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = node.*,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = .{ .standard = r.new_top },
                                                        .new_tail = .{
                                                            .checkpoint = .{
                                                                .symbol = r.new_tail,
                                                                .call_location = r.from,
                                                                .call_top = r.top,
                                                            },
                                                        },
                                                    },
                                                }),
                                            } });
                                        },
                                        .sm => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = node.*,
                                                },
                                            } });

                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                                try self.storeRule(Rule{ .standard = StandardRule{
                                                    .from = cur,
                                                    .top = .{ .standard = gamma },
                                                    .transitions = try self.arena.dupe(Transition, &.{
                                                        Transition{
                                                            .enabler = lrule.label,
                                                            .to = to,
                                                            .new_top = .{ .standard = gamma },
                                                            .old_phase = r.old_phase,
                                                            .new_phase = r.new_phase,
                                                        },
                                                    }),
                                                } });
                                            }
                                        },
                                    }
                                }
                            },
                            .exa => |node| {
                                for ((rules_by_src.get(cur.control.control_point.state) orelse continue :stack).items) |ri| {
                                    const lrule = sm_pds.rules.items[ri];
                                    switch (lrule.rule) {
                                        .int => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = node.*,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                        .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .ret => continue,
                                        .call => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .exit = .E,
                                                },
                                            } });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = .{ .standard = r.new_top },
                                                        .new_tail = .{
                                                            .symbol = .{
                                                                .ret = .{
                                                                    .symbol = r.new_tail,
                                                                    .formula = node.*,
                                                                },
                                                            },
                                                        },
                                                    },
                                                }),
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                        },
                                        .sm => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = node.*,
                                                },
                                            } });
                                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                                try self.storeRule(Rule{ .standard = StandardRule{
                                                    .from = cur,
                                                    .top = .{ .standard = gamma },
                                                    .transitions = try self.arena.dupe(Transition, &.{
                                                        Transition{
                                                            .enabler = lrule.label,
                                                            .to = to,
                                                            .new_top = .{ .standard = gamma },
                                                            .old_phase = r.old_phase,
                                                            .new_phase = r.new_phase,
                                                        },
                                                    }),
                                                } });
                                            }

                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                        },
                                    }
                                }
                            },
                            .exc => |node| {
                                const to = try self.getStateName(State{ .control = .{ .control_point = .c, .label = .{ .formula = node.* } } });
                                try stack.append(self.gpa, .{
                                    .state = to,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .to = to,
                                                .new_top = null,
                                            },
                                        }),
                                    } });
                                }
                            },
                            .axg => |node| {
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    const branches = rules_by_lhs.get(.{ .state = cur.control.control_point.state, .top = gamma }) orelse std.ArrayList(usize).empty;
                                    const transitions = try self.arena.alloc(Transition, branches.items.len);

                                    for (branches.items, 0..) |ri, ti| {
                                        const lrule = sm_pds.rules.items[ri];
                                        switch (lrule.rule) {
                                            .int => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = node.*,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                    .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                };
                                            },
                                            .ret => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = node.*,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = null,
                                                };
                                            },
                                            .call => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = node.*,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = r.new_top },
                                                    .new_tail = .{
                                                        .checkpoint = .{
                                                            .symbol = r.new_tail,
                                                            .call_location = r.from,
                                                            .call_top = r.top,
                                                        },
                                                    },
                                                };
                                            },
                                            .sm => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = node.*,
                                                    },
                                                } });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                    .old_phase = r.old_phase,
                                                    .new_phase = r.new_phase,
                                                };

                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                            },
                                        }
                                    }
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = transitions,
                                    } });
                                }
                            },
                            .axa => |node| {
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    const branches = rules_by_lhs.get(.{ .state = cur.control.control_point.state, .top = gamma }) orelse std.ArrayList(usize).empty;
                                    const transitions = try self.arena.alloc(Transition, branches.items.len);

                                    for (branches.items, 0..) |ri, ti| {
                                        const lrule = sm_pds.rules.items[ri];
                                        switch (lrule.rule) {
                                            .int => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = node.*,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                    .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                };
                                            },
                                            .ret => {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = cur.control.control_point.state },
                                                    .label = .{
                                                        .formula = .top,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                };
                                            },
                                            .call => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .exit = .Aacc,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = r.new_top },
                                                    .new_tail = .{
                                                        .symbol = .{
                                                            .ret = .{ .symbol = r.new_tail, .formula = node.* },
                                                        },
                                                    },
                                                };
                                            },
                                            .sm => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = node.*,
                                                    },
                                                } });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                    .old_phase = r.old_phase,
                                                    .new_phase = r.new_phase,
                                                };
                                            },
                                        }
                                    }
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = transitions,
                                    } });
                                }
                            },

                            .eug => |node| {
                                const to_default = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default,
                                });
                                // std.debug.print("\tAppending {f}\n", .{printer.state(to_default)});
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });

                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                for ((rules_by_src.get(cur.control.control_point.state) orelse continue :stack).items) |ri| {
                                    const lrule = sm_pds.rules.items[ri];
                                    switch (lrule.rule) {
                                        .int => |r| {
                                            try stack.append(self.gpa, .{
                                                .state = to1,
                                            });
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                        .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .ret => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .call => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = .{ .standard = r.new_top },
                                                        .new_tail = .{
                                                            .checkpoint = .{
                                                                .symbol = r.new_tail,
                                                                .call_location = r.from,
                                                                .call_top = r.top,
                                                            },
                                                        },
                                                    },
                                                }),
                                            } });
                                        },
                                        .sm => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });

                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                                try self.storeRule(Rule{ .standard = StandardRule{
                                                    .from = cur,
                                                    .top = .{ .standard = gamma },
                                                    .transitions = try self.arena.dupe(Transition, &.{
                                                        Transition{
                                                            .enabler = null,
                                                            .to = to1,
                                                            .new_top = .{ .standard = gamma },
                                                        },
                                                        Transition{
                                                            .enabler = lrule.label,
                                                            .to = to2,
                                                            .new_top = .{ .standard = gamma },
                                                            .old_phase = r.old_phase,
                                                            .new_phase = r.new_phase,
                                                        },
                                                    }),
                                                } });
                                            }
                                        },
                                    }
                                }
                            },
                            .eua => |node| {
                                const to_default = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                for ((rules_by_src.get(cur.control.control_point.state) orelse continue :stack).items) |ri| {
                                    const lrule = sm_pds.rules.items[ri];
                                    switch (lrule.rule) {
                                        .int => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                        .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .ret => {},
                                        .call => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .exit = .E,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = .{ .standard = r.new_top },
                                                        .new_tail = .{
                                                            .symbol = .{
                                                                .ret = .{
                                                                    .symbol = r.new_tail,
                                                                    .formula = f,
                                                                },
                                                            },
                                                        },
                                                    },
                                                }),
                                            } });
                                        },
                                        .sm => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });

                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                                try self.storeRule(Rule{ .standard = StandardRule{
                                                    .from = cur,
                                                    .top = .{ .standard = gamma },
                                                    .transitions = try self.arena.dupe(Transition, &.{
                                                        Transition{
                                                            .enabler = null,
                                                            .to = to1,
                                                            .new_top = .{ .standard = gamma },
                                                        },
                                                        Transition{
                                                            .enabler = lrule.label,
                                                            .to = to2,
                                                            .new_top = .{ .standard = gamma },
                                                            .old_phase = r.old_phase,
                                                            .new_phase = r.new_phase,
                                                        },
                                                    }),
                                                } });
                                            }
                                        },
                                    }
                                }
                            },
                            .erg => |node| {
                                const to_default1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                const to_default2 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default1,
                                });
                                try stack.append(self.gpa, .{
                                    .state = to_default2,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .enabler = null,
                                                .to = to_default2,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                for ((rules_by_src.get(cur.control.control_point.state) orelse continue :stack).items) |ri| {
                                    const lrule = sm_pds.rules.items[ri];
                                    switch (lrule.rule) {
                                        .int => |r| {
                                            try stack.append(self.gpa, .{
                                                .state = to1,
                                            });
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                        .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .ret => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .call => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = .{ .standard = r.new_top },
                                                        .new_tail = .{
                                                            .checkpoint = .{
                                                                .symbol = r.new_tail,
                                                                .call_location = r.from,
                                                                .call_top = r.top,
                                                            },
                                                        },
                                                    },
                                                }),
                                            } });
                                        },
                                        .sm => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });

                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                                try self.storeRule(Rule{ .standard = StandardRule{
                                                    .from = cur,
                                                    .top = .{ .standard = gamma },
                                                    .transitions = try self.arena.dupe(Transition, &.{
                                                        Transition{
                                                            .enabler = null,
                                                            .to = to1,
                                                            .new_top = .{ .standard = gamma },
                                                        },
                                                        Transition{
                                                            .enabler = lrule.label,
                                                            .to = to2,
                                                            .new_top = .{ .standard = gamma },
                                                            .old_phase = r.old_phase,
                                                            .new_phase = r.new_phase,
                                                        },
                                                    }),
                                                } });
                                            }
                                        },
                                    }
                                }
                            },
                            .era => |node| {
                                const to_default1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                const to_default2 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default1,
                                });
                                try stack.append(self.gpa, .{
                                    .state = to_default2,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .enabler = null,
                                                .to = to_default2,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                for ((rules_by_src.get(cur.control.control_point.state) orelse continue :stack).items) |ri| {
                                    const lrule = sm_pds.rules.items[ri];
                                    switch (lrule.rule) {
                                        .int => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                        .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .ret => |r| {
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                }),
                                            } });
                                        },
                                        .call => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .exit = .Eacc,
                                                },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to1,
                                                        .new_top = .{ .standard = r.top },
                                                    },
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to2,
                                                        .new_top = .{ .standard = r.new_top },
                                                        .new_tail = .{
                                                            .symbol = .{
                                                                .ret = .{
                                                                    .symbol = r.new_tail,
                                                                    .formula = f,
                                                                },
                                                            },
                                                        },
                                                    },
                                                }),
                                            } });
                                        },
                                        .sm => |r| {
                                            const to2 = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{
                                                    .formula = f,
                                                },
                                            } });

                                            try stack.append(self.gpa, .{
                                                .state = to2,
                                            });
                                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                                try self.storeRule(Rule{ .standard = StandardRule{
                                                    .from = cur,
                                                    .top = .{ .standard = gamma },
                                                    .transitions = try self.arena.dupe(Transition, &.{
                                                        Transition{
                                                            .enabler = null,
                                                            .to = to1,
                                                            .new_top = .{ .standard = gamma },
                                                        },
                                                        Transition{
                                                            .enabler = lrule.label,
                                                            .to = to2,
                                                            .new_top = .{ .standard = gamma },
                                                            .old_phase = r.old_phase,
                                                            .new_phase = r.new_phase,
                                                        },
                                                    }),
                                                } });
                                            }
                                        },
                                    }
                                }
                            },
                            .aug => |node| {
                                const to_default = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    const branches = rules_by_lhs.get(.{ .state = cur.control.control_point.state, .top = gamma }) orelse std.ArrayList(usize).empty;
                                    const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                                    transitions[0] = Transition{
                                        .enabler = null,
                                        .to = to1,
                                        .new_top = .{ .standard = gamma },
                                    };
                                    if (branches.items.len == 0) continue;

                                    for (branches.items, 1..) |ri, ti| {
                                        const lrule = sm_pds.rules.items[ri];
                                        switch (lrule.rule) {
                                            .int => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                    .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                };
                                            },
                                            .ret => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = null,
                                                };
                                            },
                                            .call => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = r.new_top },
                                                    .new_tail = .{
                                                        .checkpoint = .{
                                                            .symbol = r.new_tail,
                                                            .call_location = r.from,
                                                            .call_top = r.top,
                                                        },
                                                    },
                                                };
                                            },
                                            .sm => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });

                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                    .old_phase = r.old_phase,
                                                    .new_phase = r.new_phase,
                                                };
                                            },
                                        }
                                    }
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = transitions,
                                    } });
                                }
                            },
                            .aua => |node| {
                                const to_default = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    const branches = rules_by_lhs.get(.{ .state = cur.control.control_point.state, .top = gamma }) orelse std.ArrayList(usize).empty;
                                    const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                                    transitions[0] = Transition{
                                        .enabler = null,
                                        .to = to1,
                                        .new_top = .{ .standard = gamma },
                                    };

                                    for (branches.items, 1..) |ri, ti| {
                                        const lrule = sm_pds.rules.items[ri];
                                        switch (lrule.rule) {
                                            .int => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                    .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                };
                                            },
                                            .ret => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = .bot,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = null,
                                                };
                                            },
                                            .call => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .exit = .A,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = r.new_top },
                                                    .new_tail = .{
                                                        .symbol = .{
                                                            .ret = .{
                                                                .symbol = r.new_tail,
                                                                .formula = f,
                                                            },
                                                        },
                                                    },
                                                };
                                            },
                                            .sm => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });

                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                    .old_phase = r.old_phase,
                                                    .new_phase = r.new_phase,
                                                };
                                            },
                                        }
                                    }
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = transitions,
                                    } });
                                }
                            },
                            .arg => |node| {
                                const to_default1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                const to_default2 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default1,
                                });
                                try stack.append(self.gpa, .{
                                    .state = to_default2,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .enabler = null,
                                                .to = to_default2,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    const branches = rules_by_lhs.get(.{ .state = cur.control.control_point.state, .top = gamma }) orelse std.ArrayList(usize).empty;
                                    const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                                    transitions[0] = Transition{
                                        .enabler = null,
                                        .to = to1,
                                        .new_top = .{ .standard = gamma },
                                    };
                                    if (branches.items.len == 0) continue;

                                    for (branches.items, 1..) |ri, ti| {
                                        const lrule = sm_pds.rules.items[ri];
                                        switch (lrule.rule) {
                                            .int => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                    .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                };
                                            },
                                            .ret => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = null,
                                                };
                                            },
                                            .call => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = r.new_top },
                                                    .new_tail = .{
                                                        .checkpoint = .{
                                                            .symbol = r.new_tail,
                                                            .call_location = r.from,
                                                            .call_top = r.top,
                                                        },
                                                    },
                                                };
                                            },
                                            .sm => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });

                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                    .old_phase = r.old_phase,
                                                    .new_phase = r.new_phase,
                                                };
                                            },
                                        }
                                    }
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = transitions,
                                    } });
                                }
                            },
                            .ara => |node| {
                                const to_default1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                const to_default2 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default1,
                                });
                                try stack.append(self.gpa, .{
                                    .state = to_default2,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .enabler = null,
                                                .to = to_default2,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    const branches = rules_by_lhs.get(.{ .state = cur.control.control_point.state, .top = gamma }) orelse std.ArrayList(usize).empty;
                                    const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                                    transitions[0] = Transition{
                                        .enabler = null,
                                        .to = to1,
                                        .new_top = .{ .standard = gamma },
                                    };

                                    for (branches.items, 1..) |ri, ti| {
                                        const lrule = sm_pds.rules.items[ri];
                                        switch (lrule.rule) {
                                            .int => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                    .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                };
                                            },
                                            .ret => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = .top,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = null,
                                                };
                                            },
                                            .call => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .exit = .Aacc,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = r.new_top },
                                                    .new_tail = .{
                                                        .symbol = .{
                                                            .ret = .{
                                                                .symbol = r.new_tail,
                                                                .formula = f,
                                                            },
                                                        },
                                                    },
                                                };
                                            },
                                            .sm => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .formula = f,
                                                    },
                                                } });

                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                    .old_phase = r.old_phase,
                                                    .new_phase = r.new_phase,
                                                };
                                            },
                                        }
                                    }
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = transitions,
                                    } });
                                }
                            },

                            // .exc => |node| {
                            //     for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            //         const to = try self.getStateName(State{ .control = .{
                            //             .control_point = .c,
                            //             .label = .{ .formula = node.* },
                            //         }});
                            //         try stack.append(self.gpa, .{.state = to, .phase= cur_phase});
                            //         try self.storeRule(Rule{
                            //             .standard = .{
                            //                 .from = cur,
                            //                 .top = gamma,
                            //                 .transitions = try self.arena.dupe(Transition, &.{Transition{
                            //                     .to = to,
                            //                     .new_top = null,
                            //                 }}),
                            //             },
                            //         }, cur_phase);
                            //     }
                            // },
                            .euc => |node| {
                                const to_default = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });

                                const to2 = try self.getStateName(State{ .control = .{
                                    .control_point = .c,
                                    .label = .{
                                        .formula = f,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to2,
                                });

                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .enabler = null,
                                                .to = to2,
                                                .new_top = null,
                                            },
                                        }),
                                    } });
                                }
                            },
                            .erc => |node| {
                                const to_default1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.left,
                                    },
                                } });
                                const to_default2 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to_default1,
                                });
                                try stack.append(self.gpa, .{
                                    .state = to_default2,
                                });
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to_default1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .enabler = null,
                                                .to = to_default2,
                                                .new_top = .{ .standard = gamma },
                                            },
                                        }),
                                    } });
                                }
                                const to1 = try self.getStateName(State{ .control = .{
                                    .control_point = cur.control.control_point,
                                    .label = .{
                                        .formula = node.right,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to1,
                                });

                                const to2 = try self.getStateName(State{ .control = .{
                                    .control_point = .c,
                                    .label = .{
                                        .formula = f,
                                    },
                                } });
                                try stack.append(self.gpa, .{
                                    .state = to2,
                                });

                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .enabler = null,
                                                .to = to1,
                                                .new_top = .{ .standard = gamma },
                                            },
                                            Transition{
                                                .enabler = null,
                                                .to = to2,
                                                .new_top = null,
                                            },
                                        }),
                                    } });
                                }
                            },
                            else => {
                                @panic(try std.fmt.allocPrint(self.arena, "Unsupported operator {s}", .{@tagName(f)}));
                            },
                        }
                    },
                    .exit => |e| {
                        switch (e) {
                            .E, .Eacc => {
                                for ((rules_by_src.get(cur.control.control_point.state) orelse continue :stack).items) |ri| {
                                    const lrule = sm_pds.rules.items[ri];
                                    switch (lrule.rule) {
                                        .int => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{ .exit = e },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                        .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .ret => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{ .exit = e },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = null,
                                                    },
                                                }),
                                            } });
                                        },
                                        .call => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{ .exit = e },
                                            } });
                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            try self.storeRule(Rule{ .standard = StandardRule{
                                                .from = cur,
                                                .top = .{ .standard = r.top },
                                                .transitions = try self.arena.dupe(Transition, &.{
                                                    Transition{
                                                        .enabler = lrule.label,
                                                        .to = to,
                                                        .new_top = .{ .standard = r.new_top },
                                                        .new_tail = .{
                                                            .symbol = .{
                                                                .standard = r.new_tail,
                                                            },
                                                        },
                                                    },
                                                }),
                                            } });
                                        },
                                        .sm => |r| {
                                            const to = try self.getStateName(State{ .control = .{
                                                .control_point = .{ .state = r.to },
                                                .label = .{ .exit = e },
                                            } });

                                            try stack.append(self.gpa, .{
                                                .state = to,
                                            });
                                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                                try self.storeRule(Rule{ .standard = StandardRule{
                                                    .from = cur,
                                                    .top = .{ .standard = gamma },
                                                    .transitions = try self.arena.dupe(Transition, &.{
                                                        Transition{
                                                            .enabler = lrule.label,
                                                            .to = to,
                                                            .new_top = .{ .standard = gamma },
                                                            .old_phase = r.old_phase,
                                                            .new_phase = r.new_phase,
                                                        },
                                                    }),
                                                } });
                                            }
                                        },
                                    }
                                }
                            },
                            .A, .Aacc => {
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    const branches = rules_by_lhs.get(.{ .state = cur.control.control_point.state, .top = gamma }) orelse std.ArrayList(usize).empty;
                                    const transitions = try self.arena.alloc(Transition, branches.items.len);

                                    for (branches.items, 0..) |ri, ti| {
                                        const lrule = sm_pds.rules.items[ri];
                                        switch (lrule.rule) {
                                            .int => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{ .exit = e },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = if (r.new_top) |nt| .{ .standard = nt } else null,
                                                    .new_tail = if (r.new_tail) |nt| .{ .symbol = .{ .standard = nt } } else null,
                                                };
                                            },
                                            .ret => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .exit = e,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = null,
                                                };
                                            },
                                            .call => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .exit = e,
                                                    },
                                                } });
                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = r.new_top },
                                                    .new_tail = .{
                                                        .symbol = .{
                                                            .standard = r.new_tail,
                                                        },
                                                    },
                                                };
                                            },
                                            .sm => |r| {
                                                const to = try self.getStateName(State{ .control = .{
                                                    .control_point = .{ .state = r.to },
                                                    .label = .{
                                                        .exit = e,
                                                    },
                                                } });

                                                try stack.append(self.gpa, .{
                                                    .state = to,
                                                });
                                                transitions[ti] = Transition{
                                                    .enabler = lrule.label,
                                                    .to = to,
                                                    .new_top = .{ .standard = gamma },
                                                    .old_phase = r.old_phase,
                                                    .new_phase = r.new_phase,
                                                };
                                            },
                                        }
                                    }
                                    try self.storeRule(Rule{ .standard = StandardRule{
                                        .from = cur,
                                        .top = .{ .standard = gamma },
                                        .transitions = transitions,
                                    } });
                                }
                            },
                        }
                    },
                }
            }

            // std.debug.print("DFA OFFSET {}", .{processor.DFA.getOffset()});
            // std.debug.print("PUSHED X {}", .{self.pushed_checkpoints.keys().len});
            //
            for (dfa_states.keys()) |dfa_state| {
                for (self.pushed_checkpoints.keys()) |ch| {
                    try self.storeRuleNoCheckpoint(Rule{
                        .discard = .{
                            .from = .{ .ama = dfa_state },
                            .top = ch.checkpoint,
                            .to = .{ .ama = dfa_state },
                            .new_top = .{ .standard = ch.checkpoint.symbol },
                        },
                    });
                }
                for (self.pushed_ret_symbols.keys()) |ret| {
                    try self.storeRuleNoCheckpoint(Rule{
                        .standard = .{
                            .from = .{ .ama = dfa_state },
                            .top = .{ .ret = ret },
                            .transitions = try self.arena.dupe(Transition, &.{Transition{
                                .to = .{ .ama = dfa_state },
                                .new_top = .{ .standard = ret.symbol },
                            }}),
                        },
                    });
                }
            }

            for (0..stack.set.count()) |i| {
                const cur_pair = stack.set.keys()[i];
                const cur = cur_pair.state;
                switch (cur.control.control_point) {
                    .c => {
                        for (self.pushed_checkpoints.keys()) |ch| {
                            const to = try self.getStateName(State{ .control = .{
                                .control_point = .{ .state = ch.checkpoint.call_location },
                                .label = cur.control.label,
                            } });
                            try stack.append(self.gpa, .{ .state = to });
                            try self.storeRuleNoCheckpoint(Rule{
                                .restore = .{
                                    .from = cur,
                                    .top = ch.checkpoint,
                                    .to = to,
                                    .new_top = .{ .standard = ch.checkpoint.call_top },
                                },
                            });
                        }
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRuleNoCheckpoint(Rule{
                                .standard = .{
                                    .from = cur,
                                    .top = .{ .standard = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{
                                        Transition{
                                            .to = cur,
                                            .new_top = null,
                                        },
                                    }),
                                },
                            });
                        }
                    },
                    .state => |state| {
                        if (!ret_rules.contains(state)) continue;
                        switch (cur.control.label) {
                            .formula => {
                                for (self.pushed_checkpoints.keys()) |ch| {
                                    try self.storeRuleNoCheckpoint(Rule{
                                        .discard = .{
                                            .from = cur,
                                            .top = ch.checkpoint,
                                            .to = cur,
                                            .new_top = .{ .standard = ch.checkpoint.symbol },
                                        },
                                    });
                                }
                            },

                            .exit => {
                                for (self.pushed_ret_symbols.keys()) |ret| {
                                    const to = try self.getStateName(State{ .control = .{
                                        .control_point = .{ .state = state },
                                        .label = .{ .formula = ret.formula },
                                    } });
                                    try stack.append(self.gpa, .{
                                        .state = to,
                                    });
                                    try self.storeRuleNoCheckpoint(Rule{
                                        .standard = .{
                                            .from = cur,
                                            .top = .{ .ret = ret },
                                            .transitions = try self.arena.dupe(Transition, &.{Transition{
                                                .to = to,
                                                .new_top = .{ .standard = ret.symbol },
                                            }}),
                                        },
                                    });
                                }
                            },
                        }
                    },
                }
            }

            if (num_rules == self.rule_set.count()) break;
            try self.simplifyPostStar(self.gpa, init_state);
        }
        root.recordTime("GBPDS construction end", .{});

        for (self.state_names.keys()) |sn| {
            var contains = false;
            // std.debug.print("Check start\n", .{});
            for (visited_states.keys()) |vs| {
                // std.debug.print("Compare: {f} vs {f}\n", .{ printer.state(sn), printer.state(vs.state) });

                if (std.meta.eql(vs.state, sn)) contains = true;
            }
            if (!contains) {
                // You created a new state and did not put it on the stack. DO NOT DELETE THIS CHECK!!!
                // Instead, fix the bug
                @panic(try std.fmt.allocPrint(self.arena, "State {f} was not processed", .{printer.state(sn)}));
            }
        }

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Constrution of normal rules finished ({} ret symbols and {} ret rules): {d:.3}s", .{
                self.pushed_ret_symbols.count(),
                ret_rules.count(),
                @as(f64, @floatFromInt(root.state.timer.read())) / 1000000000,
            });
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
        new_top: SymbolOrCheckpoint,
    };

    pub const Node = union(enum) {
        int: InternalNode,
        st: StateNode,
        add: AdditionalNode,
    };

    pub const EdgeSymbol = union(enum) {
        symbol: SymbolOrCheckpoint,
        eps: void,
    };

    pub const Edge = struct {
        from: Node,
        symbol: EdgeSymbol,
        to: Node,
    };

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

    fn constructPostStar(self: *@This(), gpa: std.mem.Allocator, system: *const SM_GBPDS_Processor) !void {
        var trans = StackSet(Handle(Edge)){};
        defer trans.deinit(gpa);

        var rules_by_lhs = std.AutoHashMapUnmanaged(struct { src: State, top: SymbolOrCheckpoint }, std.ArrayList(Handle(Rule))){};
        defer {
            var it = rules_by_lhs.valueIterator();
            while (it.next()) |itt| {
                itt.deinit(gpa);
            }
            rules_by_lhs.deinit(gpa);
        }

        for (system.rule_array.items, 0..) |r, ri| {
            const rh = Handle(Rule){
                .index = @intCast(ri),
            };
            switch (r) {
                .standard => |rr| {
                    const gop = try rules_by_lhs.getOrPutValue(gpa, .{ .src = rr.from, .top = .{ .symbol = rr.top } }, .empty);
                    try gop.value_ptr.append(gpa, rh);
                },
                .restore => |rr| {
                    const gop = try rules_by_lhs.getOrPutValue(gpa, .{ .src = rr.from, .top = .{ .checkpoint = rr.top } }, .empty);
                    try gop.value_ptr.append(gpa, rh);
                },
                .discard => |rr| {
                    const gop = try rules_by_lhs.getOrPutValue(gpa, .{ .src = rr.from, .top = .{ .checkpoint = rr.top } }, .empty);
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
                    const rules_lhs = rules_by_lhs.get(.{ .src = e.from.st.state, .top = es }) orelse std.ArrayList(Handle(Rule)).empty;
                    for (rules_lhs.items) |rh| {
                        const r = system.rule_array.items[rh.index];
                        switch (r) {
                            .standard => |rule| {
                                for (rule.transitions) |t| {
                                    if (t.new_top == null) {
                                        const new_edge = try self.addEdge(gpa, .{ .from = .{ .st = .{ .state = t.to } }, .symbol = .eps, .to = e.to });
                                        try trans.append(gpa, new_edge);
                                    } else if (t.new_tail == null) {
                                        const new_edge = try self.addEdge(gpa, .{
                                            .from = .{ .st = .{ .state = t.to } },
                                            .symbol = .{ .symbol = .{ .symbol = t.new_top.? } },
                                            .to = e.to,
                                        });
                                        try trans.append(gpa, new_edge);
                                    } else {
                                        const new_edge = try self.addEdge(gpa, .{
                                            .from = .{ .st = .{ .state = t.to } },
                                            .symbol = .{ .symbol = .{ .symbol = t.new_top.? } },
                                            .to = .{ .add = .{ .trg = t.to, .new_top = .{ .symbol = t.new_top.? } } },
                                        });
                                        try trans.append(gpa, new_edge);
                                        const add_edge = try self.addEdge(gpa, .{
                                            .from = .{ .add = .{ .trg = t.to, .new_top = .{ .symbol = t.new_top.? } } },
                                            .symbol = .{ .symbol = t.new_tail.? },
                                            .to = e.to,
                                        });
                                        _ = add_edge;

                                        const eps_edges = self.eps_edges.get(.{ .trg = t.to, .new_top = .{ .symbol = t.new_top.? } }) orelse std.AutoArrayHashMapUnmanaged(Handle(Edge), void).empty;
                                        for (eps_edges.keys()) |releh| {
                                            const rele = self.getEdge(releh);
                                            const new_add_edge = try self.addEdge(gpa, .{ .from = rele.from, .symbol = .{ .symbol = t.new_tail.? }, .to = e.to });
                                            try trans.append(gpa, new_add_edge);
                                        }
                                    }
                                }
                            },
                            .restore => |rule| {
                                const new_edge = try self.addEdge(gpa, .{
                                    .from = .{ .st = .{ .state = rule.to } },
                                    .symbol = .{ .symbol = .{ .symbol = rule.new_top } },
                                    .to = e.to,
                                });
                                try trans.append(gpa, new_edge);
                            },
                            .discard => |rule| {
                                const new_edge = try self.addEdge(gpa, .{
                                    .from = .{ .st = .{ .state = rule.to } },
                                    .symbol = .{ .symbol = .{ .symbol = rule.new_top } },
                                    .to = e.to,
                                });
                                try trans.append(gpa, new_edge);
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

const parser = @import("parser.zig");

test "sm-gbpds construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var proc = processor.SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(allocator, "examples/process_test_simple.smpds");

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const ini = try proc.getInit(unprocessed_conf.init);

    var p_pre_ma = processor.MA.init(allocator, std.testing.allocator);
    defer p_pre_ma.deinit();

    var gbpds = SM_GBPDS_Processor.init(std.testing.allocator, allocator);
    defer gbpds.deinit();

    const formula = try processor.processCaret(allocator, unprocessed_conf.branchcaret.formula);

    const closure = try formula.get_closure(std.testing.allocator);
    defer {
        for (closure) |f| {
            f.deinit(std.testing.allocator);
        }
        std.testing.allocator.free(closure);
    }

    var lambda = try processor.LabellingFunction.init(std.testing.allocator, &proc, formula, processor.LabellingFunction.strict, unprocessed_conf.branchcaret.valuations);
    defer lambda.deinit();
    var ginits = std.ArrayList(State){};
    defer ginits.deinit(allocator);
    try ginits.append(allocator, State{ .control = .{ .control_point = .{ .state = ini.state }, .label = .{ .formula = formula } } });

    try gbpds.construct_optimized(&proc, closure, lambda, ginits.items[0], ini.phase, &p_pre_ma);

    var printer = try SM_GBPDS_Printer.init(std.testing.allocator, &proc);
    defer printer.deinit();

    // try std.testing.expectEqual(2, gbpds.accept_atoms.len);

    // for (gbpds.accept_atoms, 0..) |l, i| {
    //     std.debug.print("{}:\n", .{i});
    //     for (l.keys()) |a| {
    //         std.debug.print("\t{}\n", .{a.*});
    //     }
    // }

    // for (gbpds.rule_array.items) |rule| {
    //     std.debug.print("{f}\n", .{printer.rule(rule)});
    // }
}

// This is a nice idea to precompile formula like SPIN, but it is impossible
// because comptime allocations don't work

// test "comptime closure" {
//     comptime {
//         var buf: [1000000]u8 = undefined;
//         var fba = std.heap.FixedBufferAllocator.init(&buf);
//         const alloc = fba.allocator();

//         const Caret = processor.Caret;
//         const formula = Caret.Formula{
//             .ug = &Caret.Ug{
//                 .left = Caret.Formula{ .top = {} },
//                 .right = Caret.Formula{
//                     .at = &Caret.At{ .name = "123" },
//                 },
//             },
//         };

//         const closure: []const Caret.Formula = try formula.get_closure(alloc);
//         _ = closure;
//     }
// }
