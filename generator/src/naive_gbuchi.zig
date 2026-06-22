const processor = @import("processor.zig");
const hr = @import("head_reachability.zig");
const std = @import("std");
const root = @import("main.zig");

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

const Formula = processor.BranchCaret.Formula;

pub const StateLabel = union(enum) {
    formula: Formula,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        try writer.print("{f}", .{self.formula});
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

pub const Checkpoint = struct {
    symbol: processor.Symbol,
    call_location: processor.State,
    call_top: processor.Symbol,
};

pub const Symbol = processor.Symbol;

pub const SymbolOrCheckpoint = union(enum) {
    checkpoint: Checkpoint,
    symbol: Symbol,
};

pub const PSTransition = struct {
    to: processor.State,
    new_top: ?Symbol,
    new_tail: ?SymbolOrCheckpoint = null,
};

pub const Transition = struct {
    to: State,
    new_top: ?SymbolOrCheckpoint,
    new_tail: ?SymbolOrCheckpoint = null,
};

pub const Rule = struct {
    from: State,
    top: SymbolOrCheckpoint,
    transitions: []Transition,

    pub const HashContext = struct {
        pub fn hash(_: HashContext, v: Rule) u32 {
            var h = std.hash.Wyhash.init(0);
            std.hash.autoHashStrat(&h, v, .Deep);
            return @truncate(h.final());
        }

        pub fn eql(_: HashContext, a: Rule, b: Rule, _: usize) bool {
            const r1 = a;
            const r2 = b;
            if (!std.meta.eql(r1.from, r2.from)) return false;
            if (!std.meta.eql(r1.top, r2.top)) return false;
            if (r1.transitions.len != r2.transitions.len) return false;

            for (r1.transitions, r2.transitions) |t1, t2| {
                if (!std.meta.eql(t1, t2)) return false;
            }
            return true;
        }
    };
};

pub const StateName = *const State;

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
        const rule = self.rule;
        try writer.print("{f} {f} -[", .{ self.printer.state(rule.from), self.printer.symbol(rule.top) });
        try writer.print("]-> {{", .{});
        for (rule.transitions) |trans| {
            if (trans.new_top) |t| {
                if (trans.new_tail) |tt| {
                    try writer.print("{f} {f} {f}, ", .{ self.printer.state(trans.to), self.printer.symbol(t), self.printer.symbol(tt) });
                } else {
                    try writer.print("{f} {f}, ", .{ self.printer.state(trans.to), self.printer.symbol(t) });
                }
            } else {
                try writer.print("{f}, ", .{self.printer.state(trans.to)});
            }
        }
        try writer.print("}}", .{});
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
                try writer.print("{s}", .{self.printer.symbol_names.get(sym).?});
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

    pub fn init(gpa: std.mem.Allocator, proc: *processor.SM_PDS_Processor) !SM_GBPDS_Printer {
        var state_names = std.AutoHashMap(processor.State, []const u8).init(gpa);
        for (proc.states.state_map.keys()) |name| {
            try state_names.put(proc.states.state_map.get(name).?, name);
        }

        var symbol_names = std.AutoHashMap(processor.Symbol, []const u8).init(gpa);
        for (proc.symbols.symbol_map.keys()) |name| {
            try symbol_names.put(proc.symbols.symbol_map.get(name).?, name);
        }

        return SM_GBPDS_Printer{
            .proc = proc,
            .state_names = state_names,
            .symbol_names = symbol_names,
        };
    }

    pub fn deinit(self: *@This()) void {
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

    pub fn state(self: @This(), s: State) StatePrinter {
        return StatePrinter{
            .printer = self,
            .state = s,
        };
    }
};

pub const SM_GBPDS_Processor = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    state_names: std.AutoArrayHashMap(State, void),

    // symbols: std.SinglyLinkedList(Symbol),
    // symbol_names: std.AutoArrayHashMap(Symbol, SymbolName),

    rule_set: std.ArrayHashMap(Rule, void, Rule.HashContext, true),
    rule_array: std.ArrayList(Rule),

    sm_pds_proc: ?*const processor.SM_PDS_Processor,
    pushed_checkpoints: std.AutoArrayHashMap(Checkpoint, void),

    rules_by_lhs: std.AutoHashMap(StateTop, std.ArrayList(usize)),

    pre_ma: *processor.MA,

    ps_returns: std.AutoHashMap(StateTop, std.ArrayList(StateTop)),
    gl_transitions: std.AutoHashMap(StateTop, std.ArrayList(PSTransition)),
    abs_transitions: std.AutoHashMap(StateTop, std.ArrayList(PSTransition)),
    abs_defined: std.AutoHashMap(StateTop, bool),

    pub fn init(gpa: std.mem.Allocator, arena: std.mem.Allocator, pre_ma: *processor.MA) SM_GBPDS_Processor {
        return SM_GBPDS_Processor{
            .arena = arena,
            .gpa = gpa,

            // .states = std.SinglyLinkedList(State){},
            .state_names = std.AutoArrayHashMap(State, void).init(gpa),

            .ps_returns = std.AutoHashMap(StateTop, std.ArrayList(StateTop)).init(gpa),

            .gl_transitions = std.AutoHashMap(StateTop, std.ArrayList(PSTransition)).init(gpa),
            .abs_transitions = std.AutoHashMap(StateTop, std.ArrayList(PSTransition)).init(gpa),
            .abs_defined = std.AutoHashMap(StateTop, bool).init(gpa),
            // .symbols = std.SinglyLinkedList(Symbol){},
            // .symbol_names = std.AutoArrayHashMap(Symbol, SymbolName).init(gpa),

            // .rule_set = std.AutoArrayHashMap(Rule, void).init(gpa),
            .rule_set = std.ArrayHashMap(Rule, void, Rule.HashContext, true).init(gpa),
            .rule_array = .{},
            .pushed_checkpoints = std.AutoArrayHashMap(Checkpoint, void).init(gpa),
            .rules_by_lhs = std.AutoHashMap(StateTop, std.ArrayList(usize)).init(gpa),

            .sm_pds_proc = null,
            .pre_ma = pre_ma,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.state_names.deinit();
        // self.symbol_names.deinit();
        self.rule_set.deinit();
        self.rule_array.deinit(self.gpa);
        self.pushed_checkpoints.deinit();
        {
            var it = self.rules_by_lhs.iterator();
            while (it.next()) |k| {
                k.value_ptr.deinit(self.gpa);
            }
            self.rules_by_lhs.deinit();
        }

        {
            var it = self.ps_returns.valueIterator();
            while (it.next()) |k| {
                k.deinit(self.gpa);
            }
            self.ps_returns.deinit();
        }
        {
            var it = self.gl_transitions.valueIterator();
            while (it.next()) |k| {
                k.deinit(self.gpa);
            }
            self.gl_transitions.deinit();
        }
        {
            var it = self.abs_transitions.valueIterator();
            while (it.next()) |k| {
                k.deinit(self.gpa);
            }
            self.abs_transitions.deinit();
        }
        self.abs_defined.deinit();
    }

    pub fn getStateName(self: *@This(), state: State) !State {
        try self.state_names.put(state, {});
        return state;
    }

    pub fn storeRule(self: *@This(), rule: Rule) !void {
        if (self.rule_set.contains(rule)) return;
        if (rule.transitions.len == 0) return;
        try self.rule_set.putNoClobber(rule, {});
        try self.rule_array.append(self.gpa, rule);

        const r = rule;
        for (r.transitions) |t| {
            if (t.new_tail) |nt| {
                switch (nt) {
                    .symbol => {},
                    .checkpoint => |ch| {
                        try self.pushed_checkpoints.put(ch, {});
                    },
                }
            }
        }
    }

    const StateTop = struct {
        state: processor.State,
        top: processor.Symbol,
    };

    pub fn getPSReturns(self: *@This(), state: processor.State, top: processor.Symbol) !std.ArrayList(StateTop) {
        const gop = try self.ps_returns.getOrPut(.{ .state = state, .top = top });
        if (gop.found_existing) {
            return gop.value_ptr.*;
        }

        var res = std.ArrayList(StateTop){};

        rules_blk: {
            for ((self.rules_by_lhs.get(.{ .state = state, .top = top }) orelse break :rules_blk).items) |ri| {
                const rule = self.sm_pds_proc.?.system.?.rules.items[ri];
                switch (rule.rule) {
                    .call => |r| {
                        const paths = try self.pre_ma.hasPath(self.gpa, .{ .state = r.to }, &.{r.new_top});
                        defer self.gpa.free(paths);

                        for (paths) |pr| {
                            if (pr.end_node == .state) {
                                try res.append(self.gpa, .{ .state = pr.end_node.state, .top = r.new_tail });
                            }
                        }
                    },
                    .sm => unreachable,
                    else => {},
                }
            }
        }

        gop.value_ptr.* = res;
        return res;
    }

    pub fn getGlTransitions(self: *@This(), state: processor.State, top: processor.Symbol) !std.ArrayList(PSTransition) {
        const gop = try self.gl_transitions.getOrPut(.{ .state = state, .top = top });
        if (gop.found_existing) {
            return gop.value_ptr.*;
        }

        var res = std.ArrayList(PSTransition){};

        rules_blk: {
            for ((self.rules_by_lhs.get(.{ .state = state, .top = top }) orelse break :rules_blk).items) |ri| {
                const rule = self.sm_pds_proc.?.system.?.rules.items[ri];
                switch (rule.rule) {
                    .sm => unreachable,
                    .call => |r| {
                        try res.append(self.gpa, .{ .to = r.to, .new_top = r.new_top, .new_tail = .{
                            .checkpoint = .{
                                .symbol = r.new_tail,
                                .call_location = r.from,
                                .call_top = r.top,
                            },
                        } });
                    },
                    .int => |r| {
                        try res.append(self.gpa, .{ .to = r.to, .new_top = r.new_top, .new_tail = if (r.new_tail) |nt| .{ .symbol = nt } else null });
                    },
                    .ret => |r| {
                        try res.append(self.gpa, .{ .to = r.to, .new_top = null });
                    },
                }
            }
        }

        gop.value_ptr.* = res;
        return res;
    }

    pub fn getAbsTransitions(self: *@This(), state: processor.State, top: processor.Symbol) !std.ArrayList(PSTransition) {
        const gop = try self.abs_transitions.getOrPut(.{ .state = state, .top = top });
        if (gop.found_existing) {
            return gop.value_ptr.*;
        }

        var res = std.ArrayList(PSTransition){};

        rules_blk: {
            for ((self.rules_by_lhs.get(.{ .state = state, .top = top }) orelse break :rules_blk).items) |ri| {
                const rule = self.sm_pds_proc.?.system.?.rules.items[ri];
                switch (rule.rule) {
                    .sm => unreachable,
                    .call => {},
                    .int => |r| {
                        try res.append(self.gpa, .{ .to = r.to, .new_top = r.new_top, .new_tail = if (r.new_tail) |nt| .{ .symbol = nt } else null });
                    },
                    .ret => {},
                }
            }
        }
        const returns = try self.getPSReturns(state, top);
        try res.ensureUnusedCapacity(self.gpa, returns.items.len);
        for (returns.items) |ret| {
            try res.append(self.gpa, .{ .to = ret.state, .new_top = ret.top, .new_tail = null });
        }

        gop.value_ptr.* = res;
        return res;
    }

    pub fn alwaysAbsDefined(self: *@This(), state: processor.State, top: processor.Symbol) !bool {
        const gop = try self.abs_defined.getOrPut(.{ .state = state, .top = top });
        if (gop.found_existing) {
            return gop.value_ptr.*;
        }

        const res: bool = rules_blk: {
            for ((self.rules_by_lhs.get(.{ .state = state, .top = top }) orelse break :rules_blk true).items) |ri| {
                const rule = self.sm_pds_proc.?.system.?.rules.items[ri];
                switch (rule.rule) {
                    .sm => unreachable,
                    .call => |r| {
                        const paths = try self.pre_ma.hasPath(self.gpa, .{ .state = r.to }, &.{r.new_top});
                        defer self.gpa.free(paths);

                        for (paths) |path| {
                            if (path.end_node == .internal) {
                                break :rules_blk false;
                            }
                        }
                    },
                    .int => {},
                    .ret => {
                        break :rules_blk false;
                    },
                }
            }
            break :rules_blk true;
        };

        gop.value_ptr.* = res;
        return res;
    }

    pub fn construct_optimized(
        self: *@This(),
        sm_pds_proc: *processor.SM_PDS_Processor,
        closure: []const Formula,
        lambda: processor.LabellingFunction,
        inits: []const State,
    ) !void {
        _ = .{closure};
        const sm_pds = sm_pds_proc.system.?;

        self.sm_pds_proc = sm_pds_proc;

        var rules_by_src = std.AutoHashMap(processor.State, std.ArrayList(usize)).init(self.gpa);

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
                .sm => unreachable,
            };
            const gop = try rules_by_src.getOrPut(src);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.ArrayList(usize){};
            }
            try gop.value_ptr.append(self.gpa, i);

            switch (lr.rule) {
                .int => |r| {
                    const gop2 = try self.rules_by_lhs.getOrPutValue(.{ .state = r.from, .top = r.top }, std.ArrayList(usize){});
                    try gop2.value_ptr.append(self.gpa, i);
                },
                .call => |r| {
                    const gop2 = try self.rules_by_lhs.getOrPutValue(.{ .state = r.from, .top = r.top }, std.ArrayList(usize){});
                    try gop2.value_ptr.append(self.gpa, i);
                },
                .ret => |r| {
                    const gop2 = try self.rules_by_lhs.getOrPutValue(.{ .state = r.from, .top = r.top }, std.ArrayList(usize){});
                    try gop2.value_ptr.append(self.gpa, i);
                },
                .sm => unreachable,
            }
        }

        var visited_states = std.AutoHashMap(State, void).init(self.gpa);
        defer visited_states.deinit();

        var stack = StackSet(State){};
        defer stack.deinit(self.gpa);

        for (inits) |ini| {
            try stack.append(self.gpa, ini);
        }

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

        root.recordTime("Naive GBPDS Construction Start", .{});

        while (true) {
            const num_rules = self.rule_set.count();
            while (stack.pop()) |cur| {
                _ = try self.getStateName(cur);
                if (visited_states.contains(cur)) {
                    continue;
                }
                try visited_states.putNoClobber(cur, {});
                // check early if it is pC. If yes, don't do the big switch!
                if (cur.control.control_point == .c) {
                    try c_states.put(cur, {});
                    continue;
                }
                const f = cur.control.label.formula;
                // switch on the current state label and apply rules
                switch (cur.control.label.formula) {
                    .top => {
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            // create self loop
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{Transition{
                                    .to = cur,
                                    .new_top = .{ .symbol = gamma },
                                }}),
                            });
                        }
                    },
                    .bot => {},
                    .at => |a| {
                        if (lambda.state_aps.get(cur.control.control_point.state).?.contains(a.name)) {
                            for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {

                                // create self loop
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{Transition{
                                        .to = cur,
                                        .new_top = .{ .symbol = gamma },
                                    }}),
                                });
                            }
                        }

                        if (lambda.ap_dfas.get(a.name)) |ap_dfas| {
                            if (ap_dfas.get(cur.control.control_point.state)) |dfa_num| {
                                const dfa = lambda.dfas.items[dfa_num];
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    try self.storeRule(Rule{
                                        .from = cur,
                                        .top = .{ .symbol = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{Transition{
                                            .to = .{ .ama = dfa.start },
                                            .new_top = .{ .symbol = gamma },
                                        }}),
                                    });
                                }

                                for (dfa.edges.items) |edge| {
                                    try self.storeRule(Rule{
                                        .from = .{ .ama = edge.from },
                                        .top = .{ .symbol = self.sm_pds_proc.?.symbols.symbol_map.get(edge.sym).? },
                                        .transitions = try self.arena.dupe(Transition, &.{Transition{
                                            .to = .{ .ama = edge.to },
                                            .new_top = null,
                                        }}),
                                    });
                                }
                                for (dfa.finish.items) |finish| {
                                    try self.storeRule(Rule{
                                        .from = .{ .ama = finish },
                                        .top = .{ .symbol = self.sm_pds_proc.?.symbols.symbol_map.get("#").? },
                                        .transitions = try self.arena.dupe(Transition, &.{Transition{
                                            .to = .{ .ama = finish },
                                            .new_top = .{ .symbol = self.sm_pds_proc.?.symbols.symbol_map.get("#").? },
                                        }}),
                                    });
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
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{Transition{
                                        .to = cur,
                                        .new_top = .{ .symbol = gamma },
                                    }}),
                                });
                            }
                        }
                        if (lambda.ap_dfas.get(a.name)) |ap_dfas| {
                            if (ap_dfas.get(cur.control.control_point.state)) |_| {
                                @panic("Negated atomic propositions with regular valuations are not implemented");
                            } else if (!negated) {
                                for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                                    // create self loop
                                    try self.storeRule(Rule{
                                        .from = cur,
                                        .top = .{ .symbol = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{Transition{
                                            .to = cur,
                                            .new_top = .{ .symbol = gamma },
                                        }}),
                                    });
                                }
                            }
                        }
                    },
                    .land => |node| {
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{ .formula = node.left },
                        } });
                        try stack.append(self.gpa, to1);
                        const to2 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{ .formula = node.right },
                        } });
                        try stack.append(self.gpa, to2);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to2,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                    },
                    .lor => |node| {
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{ .formula = node.left },
                        } });
                        try stack.append(self.gpa, to1);
                        const to2 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{ .formula = node.right },
                        } });
                        try stack.append(self.gpa, to2);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to2,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                    },
                    .exg => |node| {
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            for ((try self.getGlTransitions(cur.control.control_point.state, gamma)).items) |trans| {
                                const to = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{ .formula = node.* },
                                } });
                                try stack.append(self.gpa, to);
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{
                                        Transition{
                                            .to = to,
                                            .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                            .new_tail = trans.new_tail,
                                        },
                                    }),
                                });
                            }
                        }
                    },
                    .exa => |node| {
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            for ((try self.getAbsTransitions(cur.control.control_point.state, gamma)).items) |trans| {
                                const to = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{ .formula = node.* },
                                } });
                                try stack.append(self.gpa, to);
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{
                                        Transition{
                                            .to = to,
                                            .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                            .new_tail = trans.new_tail,
                                        },
                                    }),
                                });
                            }
                        }
                    },
                    .exc => |node| {
                        const to = try self.getStateName(State{ .control = .{ .control_point = .c, .label = .{ .formula = node.* } } });
                        try stack.append(self.gpa, to);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to,
                                        .new_top = null,
                                    },
                                }),
                            });
                        }
                    },
                    .axg => |node| {
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            const branches = try self.getGlTransitions(cur.control.control_point.state, gamma);

                            const transitions = try self.arena.alloc(Transition, branches.items.len);
                            for (branches.items, transitions) |trans, *res_trans| {
                                const to = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{ .formula = node.* },
                                } });
                                try stack.append(self.gpa, to);
                                res_trans.* = Transition{
                                    .to = to,
                                    .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                    .new_tail = trans.new_tail,
                                };
                            }

                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = transitions,
                            });
                        }
                    },
                    .axa => |node| {
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            const branches = try self.getAbsTransitions(cur.control.control_point.state, gamma);
                            const transitions = try self.arena.alloc(Transition, branches.items.len);
                            for (branches.items, transitions) |trans, *res_trans| {
                                const to = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{ .formula = node.* },
                                } });
                                try stack.append(self.gpa, to);
                                res_trans.* = Transition{
                                    .to = to,
                                    .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                    .new_tail = trans.new_tail,
                                };
                            }

                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = transitions,
                            });
                        }
                    },

                    .eug => |node| {
                        const to_default = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to_default);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.left,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            for ((try self.getGlTransitions(cur.control.control_point.state, gamma)).items) |trans| {
                                const to2 = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{
                                        .formula = f,
                                    },
                                } });
                                try stack.append(self.gpa, to2);
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{
                                        Transition{
                                            .to = to1,
                                            .new_top = .{ .symbol = gamma },
                                        },
                                        Transition{
                                            .to = to2,
                                            .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                            .new_tail = trans.new_tail,
                                        },
                                    }),
                                });
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
                        try stack.append(self.gpa, to_default);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.left,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            for ((try self.getAbsTransitions(cur.control.control_point.state, gamma)).items) |trans| {
                                const to2 = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{
                                        .formula = f,
                                    },
                                } });
                                try stack.append(self.gpa, to2);
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{
                                        Transition{
                                            .to = to1,
                                            .new_top = .{ .symbol = gamma },
                                        },
                                        Transition{
                                            .to = to2,
                                            .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                            .new_tail = trans.new_tail,
                                        },
                                    }),
                                });
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
                        try stack.append(self.gpa, to_default1);
                        try stack.append(self.gpa, to_default2);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to_default2,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            for ((try self.getGlTransitions(cur.control.control_point.state, gamma)).items) |trans| {
                                const to2 = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{
                                        .formula = f,
                                    },
                                } });
                                try stack.append(self.gpa, to2);
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{
                                        Transition{
                                            .to = to1,
                                            .new_top = .{ .symbol = gamma },
                                        },
                                        Transition{
                                            .to = to2,
                                            .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                            .new_tail = trans.new_tail,
                                        },
                                    }),
                                });
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
                        try stack.append(self.gpa, to_default1);
                        try stack.append(self.gpa, to_default2);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to_default2,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            if (try self.alwaysAbsDefined(cur.control.control_point.state, gamma)) {
                                for ((try self.getAbsTransitions(cur.control.control_point.state, gamma)).items) |trans| {
                                    const to2 = try self.getStateName(State{ .control = .{
                                        .control_point = .{ .state = trans.to },
                                        .label = .{
                                            .formula = f,
                                        },
                                    } });
                                    try stack.append(self.gpa, to2);
                                    try self.storeRule(Rule{
                                        .from = cur,
                                        .top = .{ .symbol = gamma },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .to = to1,
                                                .new_top = .{ .symbol = gamma },
                                            },
                                            Transition{
                                                .to = to2,
                                                .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                                .new_tail = trans.new_tail,
                                            },
                                        }),
                                    });
                                }
                            } else {
                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = try self.arena.dupe(Transition, &.{
                                        Transition{
                                            .to = to1,
                                            .new_top = .{ .symbol = gamma },
                                        },
                                    }),
                                });
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
                        try stack.append(self.gpa, to_default);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.left,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            const branches = try self.getGlTransitions(cur.control.control_point.state, gamma);
                            const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                            transitions[0] = Transition{
                                .to = to1,
                                .new_top = .{ .symbol = gamma },
                            };
                            if (branches.items.len == 0) continue;
                            for (branches.items, transitions[1..]) |trans, *res_trans| {
                                const to = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{ .formula = f },
                                } });
                                try stack.append(self.gpa, to);
                                res_trans.* = Transition{
                                    .to = to,
                                    .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                    .new_tail = trans.new_tail,
                                };
                            }

                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = transitions,
                            });
                        }
                    },
                    .aua => |node| {
                        const to_default = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to_default);

                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.left,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            if (try self.alwaysAbsDefined(cur.control.control_point.state, gamma)) {
                                const branches = try self.getAbsTransitions(cur.control.control_point.state, gamma);
                                const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                                transitions[0] = Transition{
                                    .to = to1,
                                    .new_top = .{ .symbol = gamma },
                                };
                                for (branches.items, transitions[1..]) |trans, *res_trans| {
                                    const to = try self.getStateName(State{ .control = .{
                                        .control_point = .{ .state = trans.to },
                                        .label = .{ .formula = f },
                                    } });
                                    try stack.append(self.gpa, to);
                                    res_trans.* = Transition{
                                        .to = to,
                                        .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                        .new_tail = trans.new_tail,
                                    };
                                }

                                try self.storeRule(Rule{
                                    .from = cur,
                                    .top = .{ .symbol = gamma },
                                    .transitions = transitions,
                                });
                            }
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
                        try stack.append(self.gpa, to_default1);
                        try stack.append(self.gpa, to_default2);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to_default2,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            const branches = try self.getGlTransitions(cur.control.control_point.state, gamma);
                            const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                            transitions[0] = Transition{
                                .to = to1,
                                .new_top = .{ .symbol = gamma },
                            };
                            if (branches.items.len == 0) continue;
                            for (branches.items, transitions[1..]) |trans, *res_trans| {
                                const to = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{ .formula = f },
                                } });
                                try stack.append(self.gpa, to);
                                res_trans.* = Transition{
                                    .to = to,
                                    .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                    .new_tail = trans.new_tail,
                                };
                            }

                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = transitions,
                            });
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
                        try stack.append(self.gpa, to_default1);
                        try stack.append(self.gpa, to_default2);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to_default2,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to1);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            const branches = try self.getAbsTransitions(cur.control.control_point.state, gamma);
                            const transitions = try self.arena.alloc(Transition, branches.items.len + 1);
                            transitions[0] = Transition{
                                .to = to1,
                                .new_top = .{ .symbol = gamma },
                            };
                            for (branches.items, transitions[1..]) |trans, *res_trans| {
                                const to = try self.getStateName(State{ .control = .{
                                    .control_point = .{ .state = trans.to },
                                    .label = .{ .formula = f },
                                } });
                                try stack.append(self.gpa, to);
                                res_trans.* = Transition{
                                    .to = to,
                                    .new_top = if (trans.new_top) |nt| .{ .symbol = nt } else null,
                                    .new_tail = trans.new_tail,
                                };
                            }

                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = transitions,
                            });
                        }
                    },

                    .euc => |node| {
                        const to_default = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to_default);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.left,
                            },
                        } });
                        try stack.append(self.gpa, to1);

                        const to2 = try self.getStateName(State{ .control = .{
                            .control_point = .c,
                            .label = .{
                                .formula = f,
                            },
                        } });
                        try stack.append(self.gpa, to2);

                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to2,
                                        .new_top = null,
                                    },
                                }),
                            });
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
                        try stack.append(self.gpa, to_default1);
                        try stack.append(self.gpa, to_default2);
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to_default1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to_default2,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                }),
                            });
                        }
                        const to1 = try self.getStateName(State{ .control = .{
                            .control_point = cur.control.control_point,
                            .label = .{
                                .formula = node.right,
                            },
                        } });
                        try stack.append(self.gpa, to1);

                        const to2 = try self.getStateName(State{ .control = .{
                            .control_point = .c,
                            .label = .{
                                .formula = f,
                            },
                        } });
                        try stack.append(self.gpa, to2);

                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to1,
                                        .new_top = .{ .symbol = gamma },
                                    },
                                    Transition{
                                        .to = to2,
                                        .new_top = null,
                                    },
                                }),
                            });
                        }
                    },
                    else => {
                        @panic(try std.fmt.allocPrint(self.arena, "Unsupported operator {s}", .{@tagName(f)}));
                    },
                }
            }

            // std.debug.print("DFA OFFSET {}", .{processor.DFA.getOffset()});
            // std.debug.print("PUSHED X {}", .{self.pushed_checkpoints.keys().len});
            //
            for (dfa_states.keys()) |dfa_state| {
                for (self.pushed_checkpoints.keys()) |ch| {
                    try self.storeRule(Rule{
                        .from = .{ .ama = dfa_state },
                        .top = .{ .checkpoint = ch },
                        .transitions = try self.arena.dupe(Transition, &.{Transition{
                            .to = .{ .ama = dfa_state },
                            .new_top = .{
                                .symbol = ch.symbol,
                            },
                        }}),
                    });
                }
            }

            for (0..stack.set.count()) |i| {
                const cur = stack.set.keys()[i];
                switch (cur.control.control_point) {
                    .c => {
                        for (self.pushed_checkpoints.keys()) |ch| {
                            const to = try self.getStateName(State{ .control = .{
                                .control_point = .{ .state = ch.call_location },
                                .label = cur.control.label,
                            } });
                            try stack.append(self.gpa, to);
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .checkpoint = ch },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = to,
                                        .new_top = .{ .symbol = ch.call_top },
                                    },
                                }),
                            });
                        }
                        for (self.sm_pds_proc.?.symbols.symbol_names.keys()) |gamma| {
                            try self.storeRule(Rule{
                                .from = cur,
                                .top = .{ .symbol = gamma },
                                .transitions = try self.arena.dupe(Transition, &.{
                                    Transition{
                                        .to = cur,
                                        .new_top = null,
                                    },
                                }),
                            });
                        }
                    },
                    .state => |state| {
                        if (!ret_rules.contains(state)) continue;
                        switch (cur.control.label) {
                            .formula => {
                                for (self.pushed_checkpoints.keys()) |ch| {
                                    try self.storeRule(Rule{
                                        .from = cur,
                                        .top = .{ .checkpoint = ch },
                                        .transitions = try self.arena.dupe(Transition, &.{
                                            Transition{
                                                .to = cur,
                                                .new_top = .{ .symbol = ch.symbol },
                                            },
                                        }),
                                    });
                                }
                            },
                        }
                    },
                }
            }

            if (num_rules == self.rule_set.count()) break;
        }

        root.recordTime("Naive GBPDS Construction End", .{});

        for (self.state_names.keys()) |sn| {
            if (!visited_states.contains(sn)) {
                // You created a new state and did not put it on the stack. DO NOT DELETE THIS CHECK!!!
                // Instead, fix the bug
                const printer = try SM_GBPDS_Printer.init(self.gpa, sm_pds_proc);
                @panic(try std.fmt.allocPrint(self.arena, "State {f} was not processed", .{printer.state(sn)}));
            }
        }

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Constrution of normal rules finished ({} ret rules): {d:.3}s", .{
                ret_rules.count(),
                @as(f64, @floatFromInt(root.state.timer.read())) / 1000000000,
            });
        }
    }
};

const parser = @import("parser.zig");

test "gbpds construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var proc = processor.SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(allocator, "examples/process_test_simple.smpds");

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const pds = try processor.translate_to_naive(std.testing.allocator, arena.allocator(), &proc, unprocessed_conf);

    var pds_proc = processor.SM_PDS_Processor.init(arena.allocator(), std.testing.allocator);
    defer pds_proc.deinit();

    try pds_proc.process(pds.smpds, pds.init);
    const ini = try pds_proc.getInit(pds.init);

    var p_pre_ma = processor.MA.init(allocator, std.testing.allocator);
    defer p_pre_ma.deinit();

    var hrg = hr.HeadReachabilityGraph.init(allocator, std.testing.allocator, &p_pre_ma, &pds_proc);
    defer hrg.deinit();

    try hrg.constructSchwoon();

    const gpa = std.testing.allocator;
    const sccs = try hrg.findRepeatingHeads(std.testing.allocator);
    defer {
        for (sccs) |scc| {
            gpa.free(scc.heads);
        }
        gpa.free(sccs);
    }

    for (sccs) |scc| {
        std.debug.print("{any}\n", .{scc.heads});
    }
    const new_edges = try hr.build_hr_pre(gpa, &p_pre_ma, sccs);
    defer gpa.free(new_edges);

    try hrg.appendSchwoon(new_edges);

    var gbpds = SM_GBPDS_Processor.init(std.testing.allocator, allocator, &p_pre_ma);
    defer gbpds.deinit();

    const formula = try processor.processCaret(allocator, unprocessed_conf.branchcaret.formula);

    const closure = try formula.get_closure(std.testing.allocator);
    defer {
        for (closure) |f| {
            f.deinit(std.testing.allocator);
        }
        std.testing.allocator.free(closure);
    }

    var lambda = try processor.LabellingFunction.init(std.testing.allocator, &pds_proc, formula, processor.LabellingFunction.naive, unprocessed_conf.branchcaret.valuations);
    defer lambda.deinit();
    var ginits = std.ArrayList(State){};
    defer ginits.deinit(allocator);
    try ginits.append(allocator, State{ .control = .{ .control_point = .{ .state = ini.state }, .label = .{ .formula = formula } } });

    try gbpds.construct_optimized(&pds_proc, closure, lambda, ginits.items);

    var printer = try SM_GBPDS_Printer.init(std.testing.allocator, &pds_proc);
    defer printer.deinit();

    // for (gbpds.rule_array.items) |r| {
    //     std.debug.print("{f}\n", .{printer.rule(r)});
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
