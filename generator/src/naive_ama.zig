const gbuchi = @import("naive_gbuchi.zig");
const processor = @import("processor.zig");
const std = @import("std");
const root = @import("main.zig");

pub const AMAInitState = struct {
    control_point: gbuchi.State,
    iter: usize,
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

pub fn MapSetContext(comptime T: type) type {
    return struct {
        pub fn hash(_: @This(), v: Set(T)) u32 {
            var sum: u32 = 0;
            for (v.items.keys()) |item| {
                sum ^= std.hash.Murmur3_32.hashUint32(item);
            }
            return sum;
        }

        pub fn eql(_: @This(), left: Set(T), right: Set(T)) bool {
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

pub fn Pair(comptime F: type, comptime S: type) type {
    return struct {
        first: F,
        second: S,
    };
}

pub const BuchiAMA = struct {
    const NodeName = u32;

    pub const Symbol = union(enum) {
        star: void,
        symbol: gbuchi.SymbolOrCheckpoint,
    };

    pub const Edge = struct {
        from: NodeName,
        symbol: ?Symbol,
        to: Set(NodeName),
    };

    pub const HashableEdgeContext = struct {
        const good_prime = 805306457;

        fn hashSymbol(hasher: *std.hash.Wyhash, s: ?Symbol) usize {
            std.hash.autoHash(hasher, s);
            return hasher.final();
        }

        pub fn hash(_: @This(), edge: Edge) usize {
            var hasher = std.hash.Wyhash.init(0);
            var set_hash: usize = 0;
            for (edge.to.items.keys()) |k| {
                set_hash ^= k *% good_prime;
            }
            std.hash.autoHash(&hasher, set_hash);

            const sym = hashSymbol(&hasher, edge.symbol);
            const res = set_hash +% (edge.from *% good_prime *% good_prime *% good_prime) +% (sym *% good_prime *% good_prime *% good_prime *% good_prime);
            return res;
        }

        pub fn eql(_: @This(), left: Edge, right: Edge) bool {
            if (left.from != right.from) {
                return false;
            }
            if (!std.meta.eql(left.symbol, right.symbol)) {
                return false;
            }
            return left.to.items.count() == right.to.items.count() and blk: {
                for (left.to.items.keys()) |item| {
                    if (!right.to.items.contains(item)) {
                        break :blk false;
                    }
                }
                break :blk true;
            };
        }
    };

    gpa: std.mem.Allocator,

    init_names: std.AutoArrayHashMap(AMAInitState, NodeName),
    arena: std.mem.Allocator,
    arena1: std.heap.ArenaAllocator,
    arena2: std.heap.ArenaAllocator,

    edges_by_head: std.AutoHashMap(Pair(NodeName, ?Symbol), std.ArrayList(*const Edge)),
    edges_by_src: std.AutoHashMap(NodeName, std.ArrayList(*const Edge)),
    edges: EdgeMap,

    cur_step_edge_num: usize = 0,

    var node_name_offset: NodeName = 0;

    const GetOrPutEdgeResult = struct {
        edge_ptr: *Edge,
        found_existing: bool,
    };
    const EdgeMap = std.HashMap(Edge, *Edge, HashableEdgeContext, 60);

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator) BuchiAMA {
        return .{
            .arena = arena,
            .gpa = gpa,
            .init_names = std.AutoArrayHashMap(AMAInitState, BuchiAMA.NodeName).init(gpa),
            .edges = EdgeMap.init(gpa),
            .edges_by_head = std.AutoHashMap(Pair(NodeName, ?Symbol), std.ArrayList(*const Edge)).init(gpa),
            .edges_by_src = std.AutoHashMap(NodeName, std.ArrayList(*const Edge)).init(gpa),

            .arena1 = std.heap.ArenaAllocator.init(std.heap.page_allocator),
            .arena2 = std.heap.ArenaAllocator.init(std.heap.page_allocator),
        };
    }

    pub fn deinit(self: *@This()) void {
        var val_it = self.edges.valueIterator();
        while (val_it.next()) |edge_node| {
            self.destroy_edge(edge_node.*);
        }
        self.edges.deinit();
        var eh_it = self.edges_by_head.valueIterator();
        while (eh_it.next()) |eh_n| {
            eh_n.deinit(self.gpa);
        }
        self.edges_by_head.deinit();
        var es_it = self.edges_by_src.valueIterator();
        while (es_it.next()) |eh_n| {
            eh_n.deinit(self.gpa);
        }
        self.edges_by_src.deinit();
        self.init_names.deinit();
        self.arena1.deinit();
        self.arena2.deinit();
    }

    pub fn add_node() NodeName {
        const name = node_name_offset;
        node_name_offset += 1;
        return name;
    }

    pub fn clear_old_step(self: *@This()) void {
        self.cur_step_edge_num = 0;
        _ = self.arena2.reset(.{ .retain_with_limit = 1024 * 1024 });
        std.mem.swap(std.heap.ArenaAllocator, &self.arena1, &self.arena2);
    }

    pub fn add_init_node(self: *@This(), init_s: AMAInitState) !NodeName {
        const name = node_name_offset;
        try self.init_names.put(init_s, name);
        node_name_offset += 1;
        return name;
    }

    pub fn get_or_put_edge_realloc(self: *@This(), old_edge: Edge, saturation: bool) !GetOrPutEdgeResult {
        // const realloc = true;
        // var tim = try std.time.Timer.start();
        // const ctx = HashableEdgeContext{};
        // const h = ctx.hash(old_edge);
        // const eql = ctx.eql(old_edge, old_edge);

        // const dur0 = tim.lap();
        // if (dur0 > 500000) {
        //     std.log.info("slow hash computation for {}/ {} items: {}ns", .{ h, dur0, eql });
        // }

        if (self.edges.get(old_edge)) |e| {
            return .{
                .found_existing = true,
                .edge_ptr = e,
            };
        }
        // var dur1 = tim.lap();
        // if (dur1 > 500000) {
        //     std.log.info("slow lookup in {} items: {}ns with {}ns for hash and eql", .{ self.edges.count(), dur1, dur0 });
        //     dur1 = 0;
        // }

        const allocator = if (!saturation) self.gpa else self.arena1.allocator();
        if (saturation) self.cur_step_edge_num += 1;

        const edge = Edge{
            .from = old_edge.from,
            .symbol = old_edge.symbol,
            .to = Set(NodeName){
                .items = try old_edge.to.items.cloneWithAllocator(allocator),
            },
        };

        // const dur2 = tim.lap();

        const edge_ptr = try allocator.create(Edge);
        edge_ptr.* = edge;

        try self.edges.putNoClobber(edge, edge_ptr);

        // const dur3 = tim.lap();

        const by_head = try self.edges_by_head.getOrPut(.{ .first = edge.from, .second = edge.symbol });
        if (!by_head.found_existing) {
            by_head.value_ptr.* = std.ArrayList(*const Edge){};
        }

        try by_head.value_ptr.append(self.gpa, edge_ptr);

        const by_src = try self.edges_by_src.getOrPut(edge.from);
        if (!by_src.found_existing) {
            by_src.value_ptr.* = std.ArrayList(*const Edge){};
        }

        try by_src.value_ptr.append(self.gpa, edge_ptr);

        // if (dur1 + dur2 + dur3 + dur4 + dur5 > 500000) {
        //     std.log.info("Slow get_or_put_edge_realloc: {} {} {} {} {} / {}ns for hash and eql / {}", .{ dur1, dur2, dur3, dur4, dur5, dur0, @as(f32, @floatFromInt(self.edges.count())) / @as(f32, @floatFromInt(self.edges.capacity())) });
        // }
        return .{
            .found_existing = false,
            .edge_ptr = edge_ptr,
        };
    }

    fn destroy_edge(self: *@This(), edge: *Edge) void {
        blk1: {
            var list = self.edges_by_head.getPtr(.{ .first = edge.from, .second = edge.symbol }).?;
            for (list.items, 0..) |it, i| {
                if (it == edge) {
                    _ = list.swapRemove(i);
                    break :blk1;
                }
            }
            @panic("Trying to destroy non existent edge");
        }
        blk2: {
            var list = self.edges_by_src.getPtr(edge.from).?;
            for (list.items, 0..) |it, i| {
                if (it == edge) {
                    _ = list.swapRemove(i);
                    break :blk2;
                }
            }
            @panic("Trying to destroy non existent edge");
        }

        edge.to.items.deinit();
    }

    pub fn remove_edge(self: *@This(), edge: *Edge) void {
        const edge_ptr_kv = self.edges.fetchRemove(edge.*).?;
        if (edge_ptr_kv.value != edge) {
            unreachable;
        }
        self.destroy_edge(edge);
    }

    pub fn add_edge(self: *@This(), edge: Edge) !void {
        _ = try self.get_or_put_edge_realloc(edge, false);
    }

    pub fn has_edge(self: *const @This(), edge: Edge) bool {
        return self.edges.contains(edge);
    }
};

pub const AMAPrettyPrinter = struct {
    buchi_printer: *const gbuchi.SM_GBPDS_Printer,
    solver: *const AMASolver,

    pub fn state(self: *const @This(), s: BuchiAMA.NodeName) AMAStatePrinter {
        return .{
            .printer = self,
            .state = s,
        };
    }

    pub fn edge(self: *const @This(), e: BuchiAMA.Edge) AMAEdgePrinter {
        return .{
            .printer = self,
            .edge = e,
        };
    }

    pub fn symbol(self: *const @This(), p: BuchiAMA.Symbol) AMASymbolPrinter {
        return .{
            .printer = self,
            .symbol = p,
        };
    }

    pub fn init_node(self: *const @This(), n: AMAInitState) InitNodePrinter {
        return .{
            .printer = self,
            .init_node = n,
        };
    }
};

pub const AMASymbolPrinter = struct {
    printer: *const AMAPrettyPrinter,
    symbol: BuchiAMA.Symbol,

    pub fn format(
        self: @This(),
        writer: *std.io.Writer,
    ) !void {
        switch (self.symbol) {
            .star => try writer.print("*", .{}),
            .symbol => |s| try writer.print("{f}", .{self.printer.buchi_printer.symbol(.{ .symbol = s })}),
            .checkpoint => |ch| try writer.print("{f}^({f})", .{ self.printer.buchi_printer.symbol(.{ .checkpoint = ch.ch }), self.printer.buchi_printer.phase(ch.phase) }),
        }
    }
};

pub const InitNodePrinter = struct {
    printer: *const AMAPrettyPrinter,
    init_node: AMAInitState,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        return writer.print("({f}, {d})^{d}", .{ self.printer.buchi_printer.state(self.init_node.control_point), self.init_node.phase, self.init_node.iter });
    }
};

pub const AMAStatePrinter = struct {
    printer: *const AMAPrettyPrinter,
    state: BuchiAMA.NodeName,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        if (self.printer.solver.init_nodes.get(self.state)) |node| {
            try writer.print("[{d}]({f})^{d}", .{ self.state, self.printer.buchi_printer.state(node.control_point), node.iter });
        } else {
            try writer.print("qf({d})", .{self.state});
        }
    }
};

pub const AMAEdgePrinter = struct {
    printer: *const AMAPrettyPrinter,
    edge: BuchiAMA.Edge,

    pub fn format(
        self: @This(),
        writer: anytype,
    ) !void {
        try writer.print("{f}", .{self.printer.state(self.edge.from)});
        if (self.edge.symbol) |sym| {
            switch (sym) {
                .symbol => |s| {
                    try writer.print("-[{}]{f}-> {{", .{ s, self.printer.buchi_printer.symbol(s) });
                },
                .star => {
                    try writer.print("-*-> {{", .{});
                },
            }
        } else {
            try writer.print("-->{{", .{});
        }

        for (self.edge.to.items.keys()) |s| {
            try writer.print("{f}, ", .{self.printer.state(s)});
        }
        try writer.print("}}", .{});
    }
};

pub const AMASolver = struct {
    arena: std.mem.Allocator,
    ama: BuchiAMA,
    sm_adpds: *gbuchi.SM_GBPDS_Processor,

    buchi_printer: ?*gbuchi.SM_GBPDS_Printer = null,
    // accept_states: std.AutoHashMap(gbuchi.State, void),

    accept_node: BuchiAMA.NodeName,
    accept_node_list: std.ArrayList(BuchiAMA.NodeName),

    // nodes_by_ctl_rule_iter: std.AutoHashMap(NodeLookup, std.ArrayList(BuchiAMA.NodeName)),
    init_nodes: std.AutoHashMap(BuchiAMA.NodeName, AMAInitState),

    edges_to_delete: std.ArrayList(*BuchiAMA.Edge),

    accept_dfa_states: std.AutoArrayHashMap(processor.DFA.Node, void),

    final_iter: usize = 0,

    gpa: std.mem.Allocator,

    const SolverError = error{
        EmptyEdgeIntoMany,
        FailedToResetArena,
    };

    const NodeLookup = struct {
        ctl: gbuchi.State,
        rule: ?processor.RuleName,
        iter: usize,
    };

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator, sm_adpds: *gbuchi.SM_GBPDS_Processor, lambda: *const processor.LabellingFunction) !AMASolver {
        const accept_node = BuchiAMA.add_node();

        const ama = BuchiAMA.init(arena, gpa);
        // var single_acc = Set(BuchiAMA.NodeName){
        //     .items = std.AutoArrayHashMap(BuchiAMA.NodeName, void).init(arena),
        // };
        // try single_acc.items.put(accept_node, {});
        var accept_list = std.ArrayList(BuchiAMA.NodeName){};
        try accept_list.append(gpa, accept_node);
        // const edge = BuchiAMA.Edge{
        //     .from = accept_node,
        //     .to = single_acc,
        //     .symbol = .star,
        // };
        // try ama.add_edge(edge);
        //

        var accept_dfa_states = std.AutoArrayHashMap(processor.DFA.Node, void).init(gpa);

        for (lambda.dfas.items) |dfa| {
            for (dfa.finish.items) |f| {
                try accept_dfa_states.put(f, {});
            }
        }

        return AMASolver{
            .arena = arena,
            .ama = ama,
            .sm_adpds = sm_adpds,
            // .accept_states = accept_states,

            .accept_node = accept_node,
            .accept_node_list = accept_list,
            // .nodes_by_ctl_rule_iter = std.AutoHashMap(NodeLookup, std.SegmentedList(BuchiAMA.NodeName, 32)).init(allocator),
            .init_nodes = std.AutoHashMap(BuchiAMA.NodeName, AMAInitState).init(gpa),
            .gpa = gpa,
            .edges_to_delete = std.ArrayList(*BuchiAMA.Edge){},
            .accept_dfa_states = accept_dfa_states,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.init_nodes.deinit();
        self.ama.deinit();
        // self.phase_manager.deinit();
        self.accept_node_list.deinit(self.gpa);
        self.accept_dfa_states.deinit();
    }

    pub inline fn get_node_name(self: *@This(), state: AMAInitState) !BuchiAMA.NodeName {
        if (state.iter == 0) {
            return self.accept_node;
        } else {
            const actual_state = state;

            if (self.ama.init_names.contains(actual_state)) {
                return self.ama.init_names.get(actual_state).?;
            } else {
                const name = try self.ama.add_init_node(actual_state);

                try self.init_nodes.put(name, actual_state);
                return name;
            }
        }
    }

    pub fn clear_step(self: *@This(), k: usize) void {
        self.ama.clear_old_step();
        if (k <= 2) {
            return;
        }
        for (self.ama.init_names.keys()) |init_state| {
            if (init_state.iter == k - 2) {
                const v = self.ama.init_names.get(init_state).?;
                _ = self.init_nodes.remove(v);
                _ = self.ama.init_names.swapRemove(init_state);
            }
        }
    }

    // pub fn get_nodes_by_ctl_rule_iter(self: *@This(), ctl: gbuchi.State, rule: gbuchi.RuleName, iter: usize) std.ArrayList(BuchiAMA.NodeName) {
    //     if (iter == 0) {
    //         return self.accept_node_list;
    //     } else {
    //         return if (self.nodes_by_ctl_rule_iter.get(NodeLookup{ .ctl = ctl, .rule = r_lookup, .iter = iter })) |list| list.constIterator(0) else (std.SegmentedList(BuchiAMA.NodeName, 32){}).constIterator(0);
    //     }
    // }

    const Input = struct {
        succ: Set(BuchiAMA.NodeName),
        cursor: usize,

        pub fn init(allocator: std.mem.Allocator, states: Set(BuchiAMA.NodeName), cursor: usize) !Input {
            const states_set = Set(BuchiAMA.NodeName){
                .items = try states.items.cloneWithAllocator(allocator),
            };
            return Input{
                .succ = states_set,
                .cursor = cursor,
            };
        }

        pub fn clone(self: @This(), allocator: std.mem.Allocator) !Input {
            return Input{
                .succ = Set(BuchiAMA.NodeName){
                    .items = try self.succ.items.cloneWithAllocator(allocator),
                },
                .cursor = self.cursor,
            };
        }
    };
    const InputContext = struct {
        const good_prime = 805306457;

        pub fn hash(_: @This(), inp: Input) usize {
            var set_hash: usize = 0;
            for (inp.succ.items.keys()) |k| {
                set_hash ^= k *% good_prime;
            }

            const res = set_hash +% (inp.cursor *% good_prime *% good_prime *% good_prime);
            return res;
        }

        pub fn eql(_: @This(), left: Input, right: Input) bool {
            if (left.cursor != right.cursor) {
                return false;
            }
            return left.succ.items.count() == right.succ.items.count() and blk: {
                for (left.succ.items.keys()) |item| {
                    if (!right.succ.items.contains(item)) {
                        break :blk false;
                    }
                }
                break :blk true;
            };
        }
    };

    pub fn isAccepting(self: @This(), state: gbuchi.State) bool {
        _ = &.{ self, state };
        switch (state) {
            .control => |s| {
                switch (s.label) {
                    .formula => |f| {
                        switch (f) {
                            .erg, .era, .erc, .arg, .ara, .arc, .top, .at, .nat => return true,
                            else => return false,
                        }
                    },
                }
            },
            .ama => |as| {
                return self.accept_dfa_states.contains(as);
            },
        }
    }

    pub fn get_paths(self: *@This(), arena: std.mem.Allocator, from: BuchiAMA.NodeName, word: []const BuchiAMA.Symbol, cur_iter: usize) !std.ArrayList(Input) {
        // var tim = try std.time.Timer.start();
        var res = std.ArrayList(Input){};

        var eval_stack = std.ArrayList(Input){};

        var cur_to = Set(BuchiAMA.NodeName){
            .items = std.AutoArrayHashMap(BuchiAMA.NodeName, void).init(arena),
        };
        try cur_to.items.put(from, {});

        const cur_succ = try Input.init(arena, cur_to, 0);

        try eval_stack.append(arena, cur_succ);

        var visited_inputs = std.HashMap(Input, void, InputContext, 80).init(arena);

        eval1: while (eval_stack.pop()) |node| {
            if (visited_inputs.contains(node)) {
                continue;
            }
            // std.debug.print("Inspecting {any} / {}\n", .{ node.succ.items.keys(), node.cursor });
            try visited_inputs.put(node, {});

            // assume equivalence with the lower level
            for (node.succ.items.keys()) |state| {
                const val = self.init_nodes.get(state);
                if (val) |init_state| {
                    if (init_state.iter > 0 and init_state.iter == cur_iter and self.isAccepting(init_state.control_point)) {
                        const lower = try self.get_node_name(AMAInitState{
                            .control_point = init_state.control_point,
                            .iter = init_state.iter - 1,
                        });

                        var eqv_input = try node.clone(arena);
                        _ = eqv_input.succ.items.swapRemove(state);
                        try eqv_input.succ.items.put(lower, {});
                        if (!visited_inputs.contains(eqv_input)) {
                            try eval_stack.append(arena, eqv_input);
                        }
                    }
                }
            }

            if (node.cursor == word.len) {
                try res.append(arena, node);
                continue;
            }

            const top = word[node.cursor];
            // std.debug.print("top = {}\n", .{top});
            var succ_sets: []std.ArrayList(Input) = try arena.alloc(std.ArrayList(Input), node.succ.items.count());
            var succ_iters: []usize = try arena.alloc(usize, node.succ.items.count());

            for (node.succ.items.keys(), 0..) |state, i| {
                succ_sets[i] = std.ArrayList(Input){};
                if (state == self.accept_node) {
                    var next_inp = try Input.init(arena, Set(BuchiAMA.NodeName){
                        .items = std.AutoArrayHashMap(BuchiAMA.NodeName, void).init(arena),
                    }, node.cursor + 1);
                    try next_inp.succ.items.put(self.accept_node, {});
                    try succ_sets[i].append(arena, next_inp);
                    continue;
                }
                const edges = self.ama.edges_by_head.get(.{ .first = state, .second = top });
                if (edges) |edge_list| {
                    for (edge_list.items) |e| {
                        // std.debug.print("{any}\n", .{.{ .first = e.from, .second = e.symbol }});
                        // std.debug.print("{}\n", .{self.ama.edges_by_head.ctx.eql(.{ .first = state, .second = top }, .{ .first = e.from, .second = e.symbol })});
                        // std.debug.print("[{*}] {}: {any}\n", .{ e, i, e.*.to.items.keys() });
                        const next_inp = try Input.init(arena, e.*.to, node.cursor + 1);
                        try succ_sets[i].append(arena, next_inp);
                    }
                }
                if (succ_sets[i].items.len > 0) {
                    succ_iters[i] = 0;
                } else {
                    continue :eval1;
                }
            }

            const succ_maxes = try arena.alloc(usize, node.succ.items.count());
            for (succ_sets, 0..) |ss, i| {
                succ_maxes[i] = ss.items.len - 1;
            }

            const pow_stack = try powerset_arr(Input).compute(arena, succ_maxes);

            for (pow_stack) |pow_list| {
                var new_input = try node.clone(arena);
                new_input.cursor = node.cursor + 1;
                // std.debug.print("Checking powerset:\n", .{});
                // for (pow_list) |pl| {
                //     std.debug.print("{any}, ", .{pl.data.succ.items.keys()});
                // }
                // std.debug.print("\n", .{});
                for (node.succ.items.keys(), 0..) |old_state, i| {
                    const repl_inp = succ_sets[i].items[pow_list[i]];
                    _ = new_input.succ.items.swapRemove(old_state);

                    for (repl_inp.succ.items.keys()) |new_state| {
                        try new_input.succ.items.put(new_state, {});
                    }
                    // std.debug.print("{} vs {} (should be {})\n", .{ new_input.dclics.capacity(), repl_inp.dclics.capacity(), self.sm_adpds.dclics.len });
                    // std.debug.print("{any}\n", .{repl_inp.succ.items.keys()});

                    // std.debug.print("{any}\n", .{repl_inp});
                }
                if (visited_inputs.contains(new_input)) {
                    continue;
                }
                if (new_input.succ.items.count() > 0) {
                    try eval_stack.append(arena, new_input);
                }
            }
        }
        // const dur = tim.lap();
        // if (dur > 500000) {
        //     std.log.info("Slow pathing: {} visited inputs for {}ns", .{ visited_inputs.count(), dur });
        // }
        return res;
    }

    pub fn powerset_arr(comptime T: type) type {
        return struct {
            const Context = struct {
                pub fn hash(_: @This(), x: []const usize) u32 {
                    var res: u32 = 0;
                    var mult: u32 = 1610612741;
                    for (x) |n| {
                        const truncated: u32 = @truncate(n);
                        res +%= mult *% truncated;
                        mult *%= mult;
                    }
                    return res;
                }

                pub fn eql(_: @This(), x: []const usize, y: []const usize, _: usize) bool {
                    return std.mem.eql(usize, x, y);
                }
            };

            pub fn computeFromArr(arena: std.mem.Allocator, arrs: []const std.ArrayList(T)) !std.ArrayList(std.ArrayList(T)) {
                const maxes = try arena.alloc(usize, arrs.len);
                for (arrs, 0..) |arr, i| {
                    maxes[i] = arr.items.len - 1;
                }
                const pow = try @This().compute(arena, maxes);

                var res = std.ArrayList(std.ArrayList(T)){};

                try res.ensureTotalCapacity(arena, pow.len);
                for (0..pow.len) |i| {
                    try res.append(arena, std.ArrayList(T){});
                    const resi = &res.items[i];
                    resi.* = std.ArrayList(T){};
                    try resi.ensureTotalCapacity(arena, arrs.len);
                    for (pow[i], 0..) |powi, j| {
                        try resi.append(arena, arrs[j].items[powi]);
                    }
                }

                return res;
            }

            pub fn compute(arena: std.mem.Allocator, maxes: []const usize) ![]const []const usize {
                // var tim = try std.time.Timer.start();

                var pow_stack = std.ArrayList([]const usize){};
                var visited = std.ArrayHashMap([]const usize, void, Context, false).init(arena);
                const init_ind = try arena.alloc(usize, maxes.len);
                for (init_ind) |*in| {
                    in.* = 0;
                }

                try pow_stack.append(arena, init_ind);

                pow_loop: while (pow_stack.pop()) |pow_list| {
                    if (visited.contains(pow_list)) {
                        continue :pow_loop;
                    }
                    try visited.put(pow_list, {});
                    for (pow_list, 0..) |child_node, i| {
                        if (child_node < maxes[i]) {
                            var next_pow = try arena.dupe(usize, pow_list);
                            next_pow[i] = child_node + 1;
                            try pow_stack.append(arena, next_pow);
                            // try visited.put(next_pow, {});
                        }
                    }
                }

                // const dur = tim.lap();
                // if (dur > 500000) {
                //     std.log.info("Slow powerset computation of {} variants for {}ns", .{ visited.count(), dur });
                // }
                return visited.keys();
            }
        };
    }
    pub fn powerset(comptime T: type) type {
        return struct {
            const Context = struct {
                pub fn hash(_: @This(), x: []const *const std.SinglyLinkedList(T).Node) u32 {
                    var res: u32 = 0;
                    var mult: u32 = 1610612741;
                    for (x) |n| {
                        const truncated: u32 = @truncate(@intFromPtr(n));
                        res +%= mult *% truncated;
                        mult *%= mult;
                    }
                    return res;
                }

                pub fn eql(_: @This(), x: []const *const std.SinglyLinkedList(T).Node, y: []const *const std.SinglyLinkedList(T).Node, _: usize) bool {
                    return std.mem.eql(*const std.SinglyLinkedList(T).Node, x, y);
                }
            };

            pub fn compute(allocator: std.mem.Allocator, nodes: []const *const std.SinglyLinkedList(T).Node) ![]const []const *const std.SinglyLinkedList(T).Node {
                // var tim = try std.time.Timer.start();

                var pow_stack = std.SegmentedList([]const *const std.SinglyLinkedList(T).Node, 1){};
                var visited = std.ArrayHashMap([]const *const std.SinglyLinkedList(T).Node, void, Context, false).init(allocator);
                try pow_stack.append(allocator, nodes);
                // try visited.put(nodes, {});

                pow_loop: while (pow_stack.pop()) |pow_list| {
                    if (visited.contains(pow_list)) {
                        continue :pow_loop;
                    }
                    try visited.put(pow_list, {});
                    for (pow_list, 0..) |child_node, i| {
                        if (child_node.next) |next_child| {
                            var next_pow = try allocator.dupe(*const std.SinglyLinkedList(T).Node, pow_list);
                            next_pow[i] = next_child;
                            try pow_stack.append(allocator, next_pow);
                            // try visited.put(next_pow, {});
                        }
                    }
                }

                // const dur = tim.lap();
                // if (dur > 500000) {
                //     std.log.info("Slow powerset computation of {} variants for {}ns", .{ visited.count(), dur });
                // }
                return visited.keys();
            }
        };
    }

    pub fn construct(self: *@This(), progress: ?std.Progress.Node) !void {
        var root_node: ?std.Progress.Node = null;
        defer if (root_node) |r| r.end();

        var k: usize = 0;
        var fixpoint_reached: bool = false;
        // var tmp_edges
        var path_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);

        defer path_arena.deinit();

        var loop1_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        defer loop1_arena.deinit();

        var states = std.AutoArrayHashMap(gbuchi.State, void).init(self.gpa);
        defer states.deinit();

        const total_states: u32 = @intCast(self.sm_adpds.state_names.count());
        // std.debug.print("We start with {} nodes\n", .{total_states});
        // std.debug.print("Total {} phases in AMA\n", .{self.sm_adpds.sm_pds_proc.?.phases.count()});
        std.log.info("We start with {} nodes", .{total_states});
        std.log.info("We have {} rules", .{self.sm_adpds.rule_array.items.len});
        {
            const init_progress = if (progress) |_| root_node.?.start("Adding initial states", total_states) else undefined;
            defer if (progress) |_| init_progress.end();
            errdefer std.log.err("Tried to allocate memory for {} nodes\n", .{total_states});
            try self.ama.init_names.ensureTotalCapacity(total_states);
            try self.init_nodes.ensureTotalCapacity(total_states);

            for (self.sm_adpds.state_names.keys()) |state| {
                if (progress) |_| init_progress.completeOne();
                _ = try self.get_node_name(AMAInitState{
                    .control_point = state,
                    .iter = 1,
                });
            }
        }

        var old_edges = std.ArrayList(*BuchiAMA.Edge){};
        defer old_edges.deinit(self.gpa);

        var cur_edges = std.ArrayList(*BuchiAMA.Edge){};
        defer cur_edges.deinit(self.gpa);

        var loop1_progress: std.Progress.Node = undefined;
        if (progress) |_| {
            loop1_progress = root_node.?.start("loop 1", 0);
        }
        defer if (progress) |_| loop1_progress.end();

        root.recordTime("Naive Loop 1 start", .{});

        // This is loop 1
        // We do not add empty transitions to the lower level,
        // but instead the function get_paths assumes the equivalence
        // with the lower level.
        while (!fixpoint_reached) {
            if (progress) |_| {
                loop1_progress.completeOne();
            }
            k += 1;
            self.clear_step(k);

            // std.debug.print("k = {any}\n", .{k});

            old_edges = cur_edges;

            defer old_edges.clearAndFree(self.gpa);

            cur_edges = std.ArrayList(*BuchiAMA.Edge){};

            if (!loop1_arena.reset(std.heap.ArenaAllocator.ResetMode.retain_capacity)) {
                return SolverError.FailedToResetArena;
            }

            // var sat_trans_addded: usize = 0;
            var saturated: bool = false;
            var saturation_steps: usize = 0;

            // This is loop 2
            while (!saturated) {
                var transitions_added: usize = 0;

                // std.log.info("{} Rules and {} phases. Total: {}", .{ self.sm_adpds.rules.count(), visited_phases_arr.items.len, self.sm_adpds.rules.count() * visited_phases_arr.items.len });
                var rules_processed: usize = 0;
                rule_loop: for (self.sm_adpds.rule_array.items) |brule| {
                    saturation_steps += 1;
                    // if (self.buchi_printer) |p| {
                    //     std.debug.print("Eval {f}\n", .{p.rule(brule)});
                    // }
                    const rule = brule;
                    // if (self.buchi_printer) |p| {
                    //     std.debug.print("Phase: {}\n", .{p.phase(phase_key)});
                    // }

                    if (!path_arena.reset(.{ .retain_with_limit = 1024 * 1024 })) {
                        return SolverError.FailedToResetArena;
                    }

                    var applied_trans = std.ArrayList(*gbuchi.Transition){};
                    const path_alloc = path_arena.allocator();
                    try applied_trans.ensureTotalCapacity(path_alloc, rule.transitions.len);

                    for (rule.transitions) |*trans| {
                        try applied_trans.append(path_alloc, trans);
                    }
                    rules_processed += 1;
                    const trg_states: []std.ArrayList(Input) = try path_arena.allocator().alloc(std.ArrayList(Input), applied_trans.items.len);

                    var j: usize = 0;

                    for (applied_trans.items) |t| {
                        const s = try self.get_node_name(AMAInitState{
                            .control_point = t.to,
                            .iter = k,
                        });
                        var word: []const BuchiAMA.Symbol = &.{};

                        if (t.new_top) |new_top| {
                            if (t.new_tail) |new_tail| {
                                word = try path_alloc.dupe(BuchiAMA.Symbol, &.{
                                    BuchiAMA.Symbol{ .symbol = new_top },
                                    BuchiAMA.Symbol{ .symbol = new_tail },
                                });
                            } else {
                                word = try path_alloc.dupe(BuchiAMA.Symbol, &.{
                                    BuchiAMA.Symbol{ .symbol = new_top },
                                });
                            }
                        } else {
                            word = &.{};
                        }
                        const paths = try self.get_paths(path_alloc, s, word, k);

                        if (paths.items.len > 0) {
                            trg_states[j] = paths;
                            j += 1;
                        } else {
                            continue :rule_loop;
                        }
                    }
                    const trg_pow = try powerset_arr(Input).computeFromArr(path_alloc, trg_states);

                    const node_name = try self.get_node_name(AMAInitState{
                        .control_point = rule.from,
                        .iter = k,
                    });

                    trg_loop: for (trg_pow.items) |trg| {
                        var trg_node = std.AutoArrayHashMap(BuchiAMA.NodeName, void).init(path_alloc);
                        var cap: usize = 0;
                        var succ_cap: usize = 0;
                        for (trg.items) |node| {
                            for (node.succ.items.keys()) |succ_k| {
                                if (succ_k != self.accept_node) {
                                    cap += 1;
                                } else {
                                    succ_cap = 1;
                                }
                            }
                        }
                        try trg_node.ensureTotalCapacity(cap + succ_cap);

                        for (trg.items) |node| {
                            for (node.succ.items.keys()) |succ_k| {
                                if (succ_k != self.accept_node) {
                                    var bstate = self.init_nodes.get(succ_k).?;
                                    bstate.iter = k;
                                    const new_node_name = try self.get_node_name(bstate);
                                    try trg_node.put(new_node_name, {});
                                } else {
                                    try trg_node.put(succ_k, {});
                                }
                            }
                        }

                        const new_edge_symbol = BuchiAMA.Symbol{ .symbol = rule.top };
                        // This is optimizations of the algorithm proposed by Fu Song
                        // They do not work correctly because of the DCLIC labels
                        //
                        // However, in BCaret, we do not have DCLICs, so it should be okay

                        const optimization_enabled = true;
                        if (optimization_enabled) {
                            var ee_num: usize = 0;
                            const existing_edges = self.ama.edges_by_head.get(.{ .first = node_name, .second = new_edge_symbol });
                            if (existing_edges) |ee| {
                                // edge_iter looks for the same edge (or edge with a subset target)
                                edge_iter: for (ee.items) |el| {
                                    ee_num += 1;
                                    // if it is not a subset, look for different edge
                                    for (el.*.to.items.keys()) |to_state| {
                                        if (!trg_node.contains(to_state)) {
                                            continue :edge_iter;
                                        }
                                    }
                                    // if it is a subset, do not create an edge and look for different target
                                    continue :trg_loop;
                                }
                            }
                        }
                        const edge_res = try self.ama.get_or_put_edge_realloc(BuchiAMA.Edge{
                            .from = node_name,
                            .symbol = new_edge_symbol,
                            .to = Set(BuchiAMA.NodeName){
                                .items = trg_node,
                            },
                        }, true);
                        if (!edge_res.found_existing) {
                            transitions_added += 1;
                            try cur_edges.append(self.gpa, edge_res.edge_ptr);
                        }
                    }
                }
                if (transitions_added == 0) {
                    saturated = true;
                }
            }
            // root.recordTime("Saturation steps {}", .{saturation_steps});
            // root.recordTime("Edges added {}", .{cur_edges.items.len});
            if (k > 1) {
                fixpoint_reached = true;
                var deleted_edges: usize = 0;
                while (old_edges.pop()) |edge| {
                    deleted_edges += 1;

                    const old_node = self.init_nodes.get(edge.from).?;

                    const new_node = try self.get_node_name(AMAInitState{
                        .control_point = old_node.control_point,
                        .iter = k,
                    });
                    var hashable = BuchiAMA.Edge{
                        .from = new_node,
                        .symbol = edge.symbol.?,
                        .to = Set(BuchiAMA.NodeName){
                            .items = std.AutoArrayHashMap(BuchiAMA.NodeName, void).init(loop1_arena.allocator()),
                        },
                    };
                    for (edge.to.items.keys()) |trg_node| {
                        if (trg_node == self.accept_node) {
                            try hashable.to.items.put(trg_node, {});
                        } else {
                            const old_trg = self.init_nodes.get(trg_node).?;

                            const new_trg = try self.get_node_name(AMAInitState{
                                .control_point = old_trg.control_point,
                                .iter = k,
                            });
                            try hashable.to.items.put(new_trg, {});
                        }
                    }
                    // if the previous step had an edge (hashable^-1) that was not added at this step (hashable)
                    if (!self.ama.has_edge(hashable)) {
                        fixpoint_reached = false;
                    }
                    // std.debug.print("Destroying {*}\n", .{edge});
                    self.ama.remove_edge(edge);
                }
            }
        }
        root.recordTime("Naive Loop 1 end", .{});
        self.final_iter = k;
        self.clear_step(k + 1);
        self.edges_to_delete = cur_edges;

        if (progress) |_| {
            std.log.info("Finished with {} edges\n", .{self.ama.edges.count()});
        }
    }
};

const parser = @import("parser.zig");

// test "power" {
//     var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
//     defer arena.deinit();
//     const allocator = arena.allocator();
//
//     const res = try AMASolver.powerset_arr(usize).compute(allocator, &.{ 1, 2, 3, 4 });
//
//     std.debug.print("{any}", .{res});
// }

const hr = @import("head_reachability.zig");
test "ama construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var proc = processor.SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(allocator, "tests/true-10.smpds");

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

    // for (sccs) |scc| {
    //     std.debug.print("{any}\n", .{scc.heads});
    // }
    const new_edges = try hr.build_hr_pre(gpa, &p_pre_ma, sccs);
    defer gpa.free(new_edges);

    try hrg.appendSchwoon(new_edges);

    var gbpds = gbuchi.SM_GBPDS_Processor.init(std.testing.allocator, allocator, &p_pre_ma);
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
    var ginits = std.ArrayList(gbuchi.State){};
    defer ginits.deinit(allocator);

    const ginit = gbuchi.State{ .control = .{ .control_point = .{ .state = ini.state }, .label = .{ .formula = formula } } };
    try ginits.append(allocator, ginit);

    try gbpds.construct_optimized(&pds_proc, closure, lambda, ginits.items);

    var printer = try gbuchi.SM_GBPDS_Printer.init(std.testing.allocator, &pds_proc);
    defer printer.deinit();

    // for (gbpds.rule_array.items) |rule| {
    //     std.debug.print("{f}\n", .{printer.rule(rule)});
    // }

    var ama_solver = try AMASolver.init(arena.allocator(), std.testing.allocator, &gbpds, &lambda);
    ama_solver.buchi_printer = &printer;

    defer ama_solver.deinit();

    try ama_solver.construct(null);

    // var ama_printer = AMAPrettyPrinter{
    //     .buchi_printer = &printer,
    //     .solver = &ama_solver,
    // };
    // std.debug.print("Edges:\n", .{});
    // var it = ama_solver.ama.edges.valueIterator();
    // while (it.next()) |edge_ptr_ptr| {
    //     // if (solver.accept_node == edge_node.data.from or ama_printer.solver.init_nodes.get(edge_node.data.from).?.iter == solver.final_iter)
    //     std.debug.print("[{*}]: {f}\n", .{ edge_ptr_ptr.*, ama_printer.edge(edge_ptr_ptr.*.*) });
    // }
    // std.debug.print("\n", .{});

    // try std.testing.expectEqual(2, gbpds.accept_atoms.len);

    // for (gbpds.accept_atoms, 0..) |l, i| {
    //     std.debug.print("{}:\n", .{i});
    //     for (l.keys()) |a| {
    //         std.debug.print("\t{}\n", .{a.*});
    //     }
    // }
    const ama_word = try gpa.alloc(BuchiAMA.Symbol, ini.stack.len + 1);
    defer gpa.free(ama_word);

    for (ama_word[0..ini.stack.len], ini.stack) |*aw, st| {
        aw.* = .{ .symbol = .{ .symbol = st } };
    }
    ama_word[ini.stack.len] = .{ .symbol = .{ .symbol = try pds_proc.process_symbol("#") } };
    // std.debug.print("finding paths...\n", .{});
    const res = try ama_solver.get_paths(arena.allocator(), try ama_solver.get_node_name(.{ .control_point = ginit, .iter = ama_solver.final_iter }), ama_word, 0);

    var result = false;
    for (res.items) |inp| {
        // std.debug.print("Found ", .{});
        // for (inp.succ.items.keys()) |st| {
        //     std.debug.print("{f},", .{ama_printer.state(st)});
        // }
        // std.debug.print("\n", .{});
        if (inp.succ.items.count() == 1 and inp.succ.items.keys()[0] == ama_solver.accept_node) {
            result = true;
        }
    }
    // if (result) {
    //     std.debug.print("True\n", .{});
    // } else {
    //     std.debug.print("False\n", .{});
    // }
}
