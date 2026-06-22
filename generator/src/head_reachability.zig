const processor = @import("processor.zig");
const std = @import("std");
const root = @import("main.zig");

pub const Head = struct {
    state: processor.State,
    top: processor.Symbol,

    index: ?u32 = null,
    lowlink: ?u32 = null,
    on_stack: ?bool = null,
};

pub const Edge = struct {
    from: *const Head,
    // label: bool,
    to: *const Head,
};

pub const HeadState = struct {
    state: processor.State,
};

pub const HeadReachabilityGraph = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    pre_ma: *processor.MA,
    sm_pds: *const processor.SM_PDS_Processor,

    heads: std.AutoArrayHashMap(Head, *Head),

    edges: std.AutoArrayHashMap(Edge, *const Edge),
    edges_by_src: std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)),
    edges_by_trg: std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)),

    heads_by_state: std.AutoHashMap(HeadState, std.AutoArrayHashMap(*const Head, void)),

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator, pre_ma: *processor.MA, sm_pds: *const processor.SM_PDS_Processor) @This() {
        return @This(){
            .arena = arena,
            .gpa = gpa,

            .pre_ma = pre_ma,
            .sm_pds = sm_pds,

            .edges = std.AutoArrayHashMap(Edge, *const Edge).init(gpa),
            .edges_by_src = std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)).init(gpa),
            .edges_by_trg = std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)).init(gpa),

            .heads_by_state = std.AutoHashMap(HeadState, std.AutoArrayHashMap(*const Head, void)).init(gpa),
            .heads = std.AutoArrayHashMap(Head, *Head).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.edges.deinit();
        {
            var it = self.edges_by_src.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }

            self.edges_by_src.deinit();
        }
        {
            var it = self.edges_by_trg.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }

            self.edges_by_trg.deinit();
        }
        {
            var it = self.heads_by_state.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }

            self.heads_by_state.deinit();
        }
        self.heads.deinit();
    }

    pub const HRErr = error{
        AddingEdgeAfterTarjan,
    };

    fn addHead(self: *@This(), head: Head) !*const Head {
        if (root.syscalls_enabled and head.index != null) {
            std.log.err("Cannot add edges after searching repeating heads!", .{});
            return HRErr.AddingEdgeAfterTarjan;
        }
        if (self.heads.get(head)) |h_ptr| {
            return h_ptr;
        }
        const head_ptr = try self.arena.create(Head);
        head_ptr.* = head;
        try self.heads.put(head, head_ptr);
        return head_ptr;
    }

    fn addEdge(self: *@This(), edge: Edge) !bool {
        if (self.edges.contains(edge)) {
            return false;
        }
        const edge_ptr = try self.arena.create(Edge);
        edge_ptr.* = edge;

        try self.edges.put(edge, edge_ptr);

        {
            const gop = try self.edges_by_trg.getOrPut(edge.to);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge_ptr, {});
        }

        {
            const gop = try self.heads_by_state.getOrPut(HeadState{ .state = edge.from.state });
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Head, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge.from, {});
        }

        {
            const gop = try self.heads_by_state.getOrPut(HeadState{ .state = edge.to.state });
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Head, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge.to, {});
        }

        return true;
    }

    pub fn constructSchwoon(self: *@This()) !void {
        defer {
            var it = self.edges_by_trg.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }
            self.edges_by_trg.clearAndFree();
        }
        //  rel = self.pre_ma

        var trans = std.ArrayList(*const processor.MA.Edge){};
        defer trans.deinit(self.gpa);

        var trans_set = std.AutoHashMap(*const processor.MA.Edge, void).init(self.gpa);
        defer trans_set.deinit();

        // delta_aux = self.edges

        const RuleTail = struct {
            to: processor.State,
            new_top: processor.Symbol, // null for self-modifying rules
        };

        var rules_by_tail = std.AutoHashMap(RuleTail, std.ArrayList(*const processor.Rule)).init(self.gpa);
        defer {
            var it = rules_by_tail.iterator();
            while (it.next()) |e| {
                e.value_ptr.deinit(self.gpa);
            }
            rules_by_tail.deinit();
        }

        for (self.sm_pds.system.?.rules.items) |*rule| {
            switch (rule.rule) {
                .sm => |_| {
                    unreachable;
                    // const tail = RuleTail{
                    //     .to = r.to,
                    //     .new_top = r.top,
                    // };
                    // const gop = try rules_by_tail.getOrPut(tail);
                    // if (!gop.found_existing) {
                    //     gop.value_ptr.* = std.ArrayList(*const processor.Rule){};
                    // }
                    // try gop.value_ptr.append(self.gpa, rule);
                },
                .int => |r| {
                    if (r.new_top == null) continue;
                    const tail = RuleTail{
                        .to = r.to,
                        .new_top = r.new_top.?,
                    };
                    const gop = try rules_by_tail.getOrPut(tail);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = std.ArrayList(*const processor.Rule){};
                    }
                    try gop.value_ptr.append(self.gpa, &rule.rule);
                },
                .call => |r| {
                    const tail = RuleTail{
                        .to = r.to,
                        .new_top = r.new_top,
                    };
                    const gop = try rules_by_tail.getOrPut(tail);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = std.ArrayList(*const processor.Rule){};
                    }
                    try gop.value_ptr.append(self.gpa, &rule.rule);
                },
                .ret => {},
            }
        }

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        for (self.sm_pds.system.?.rules.items) |rule| {
            switch (rule.rule) {
                .sm => unreachable,
                .call => {},
                .ret => |r| {
                    const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                        .from = .{ .state = r.from },
                        .symbol = r.top,
                        .to = .{ .state = r.to },
                    });
                    if (!trans_set.contains(edge_ptr)) {
                        try trans.append(self.gpa, edge_ptr);
                        try trans_set.put(edge_ptr, {});
                    }
                },
                .int => |r| {
                    if (r.new_top == null) {
                        const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                            .from = .{ .state = r.from },
                            .symbol = r.top,
                            .to = .{ .state = r.to },
                        });
                        if (!trans_set.contains(edge_ptr)) {
                            try trans.append(self.gpa, edge_ptr);
                            try trans_set.put(edge_ptr, {});
                        }
                    }
                },
            }
        }

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        while (trans.pop()) |edge| {
            if (!try self.pre_ma.addEdgePtr(edge)) {
                continue;
            }
            if (edge.from == .internal) continue;

            const hr_edges_opt = self.edges_by_trg.get(try self.addHead(Head{
                .state = edge.from.state,
                .top = edge.symbol,
            }));
            if (hr_edges_opt) |hr_edges| {
                for (hr_edges.keys()) |hr_edge| {
                    const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                        .from = .{ .state = hr_edge.from.state },
                        .symbol = hr_edge.from.top,
                        .to = edge.to,
                    });
                    if (!trans_set.contains(edge_ptr)) {
                        try trans.append(self.gpa, edge_ptr);
                        try trans_set.put(edge_ptr, {});
                    }
                }
            }

            if (rules_by_tail.get(.{ .to = edge.from.state, .new_top = edge.symbol })) |tail_rules| {
                for (tail_rules.items) |rule| {
                    switch (rule.*) {
                        .sm => {
                            unreachable;
                        },
                        .ret => unreachable,
                        .int => |r| {
                            if (r.new_tail == null) {
                                const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                                    .from = .{ .state = r.from },
                                    .symbol = r.top,
                                    .to = edge.to,
                                });
                                if (!trans_set.contains(edge_ptr)) {
                                    try trans.append(self.gpa, edge_ptr);
                                    try trans_set.put(edge_ptr, {});
                                }
                            } else {
                                _ = try self.addEdge(Edge{
                                    .from = try self.addHead(Head{
                                        .state = r.from,
                                        .top = r.top,
                                    }),
                                    .to = try self.addHead(Head{
                                        .state = edge.to.state,
                                        .top = r.new_tail.?,
                                    }),
                                });

                                const aux_edges_opt = self.pre_ma.edges_by_head.get(.{
                                    .from = edge.to,
                                    .symbol = r.new_tail.?,
                                });
                                if (aux_edges_opt) |aux_edges| {
                                    for (aux_edges.keys()) |edge_aux| {
                                        const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                                            .from = .{ .state = r.from },
                                            .symbol = r.top,
                                            .to = edge_aux.to,
                                        });
                                        if (!trans_set.contains(edge_ptr)) {
                                            try trans.append(self.gpa, edge_ptr);
                                            try trans_set.put(edge_ptr, {});
                                        }
                                    }
                                }
                            }
                        },
                        .call => |r| {
                            _ = try self.addEdge(Edge{
                                .from = try self.addHead(Head{
                                    .state = r.from,
                                    .top = r.top,
                                }),
                                .to = try self.addHead(Head{
                                    .state = edge.to.state,
                                    .top = r.new_tail,
                                }),
                            });

                            const aux_edges_opt = self.pre_ma.edges_by_head.get(.{
                                .from = edge.to,
                                .symbol = r.new_tail,
                            });
                            if (aux_edges_opt) |aux_edges| {
                                for (aux_edges.keys()) |edge_aux| {
                                    const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                                        .from = .{ .state = r.from },
                                        .symbol = r.top,
                                        .to = edge_aux.to,
                                    });
                                    if (!trans_set.contains(edge_ptr)) {
                                        try trans.append(self.gpa, edge_ptr);
                                        try trans_set.put(edge_ptr, {});
                                    }
                                }
                            }
                        },
                    }
                }
            }
        }

        {
            var it = self.edges_by_trg.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }
            self.edges_by_trg.clearAndFree();
        }
        // ------------------------------

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Adding default hr edges ({} edges currently): {d:.3}s", .{ self.edges.count(), @as(f64, @floatFromInt(root.state.timer.read())) / 1000000000 });
            std.log.info("Iterating over 1 phases and {} rules", .{self.sm_pds.system.?.rules.items.len});
        }

        for (self.sm_pds.system.?.rules.items) |rule| {
            switch (rule.rule) {
                .sm => |_| {
                    unreachable;
                    // if (!phase.items.contains(r.label)) {
                    //     continue :rule_loop;
                    // }
                    // const next_phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.get(.{
                    //     .original_phase = phase_name,
                    //     .to_add = r.new_rules,
                    //     .to_remove = r.old_rules,
                    // }) orelse continue :rule_loop; // continue because it means for rule p -(r1 / r2)-> p1 there is no r1 in phase.
                    // _ = try self.addEdge(Edge{
                    //     .from = try self.addHead(Head{
                    //         .state = r.from,
                    //         .phase = phase_name,
                    //         .top = r.top,
                    //     }),
                    //     .label = self.sm_bpds.isAccepting(r.from.*),
                    //     .to = try self.addHead(Head{
                    //         .state = r.to,
                    //         .phase = next_phase,
                    //         .top = r.top,
                    //     }),
                    // });
                },
                .int => |r| {
                    if (r.new_top != null) {
                        _ = try self.addEdge(Edge{
                            .from = try self.addHead(Head{
                                .state = r.from,
                                .top = r.top,
                            }),
                            .to = try self.addHead(Head{
                                .state = r.to,
                                .top = r.new_top.?,
                            }),
                        });
                    }
                },
                .call => |r| {
                    _ = try self.addEdge(Edge{
                        .from = try self.addHead(Head{
                            .state = r.from,
                            .top = r.top,
                        }),
                        .to = try self.addHead(Head{
                            .state = r.to,
                            .top = r.new_top,
                        }),
                    });
                },
                .ret => {},
            }
        }
        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Edges finish ({} edges and {} heads currently): {d:.3}s", .{ self.edges.count(), self.heads.count(), @as(f64, @floatFromInt(root.state.timer.read())) / 1000000000 });
        }
    }

    pub fn appendSchwoon(self: *@This(), new_edges: []const *const processor.MA.Edge) !void {
        defer {
            var it = self.edges_by_trg.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }
            self.edges_by_trg.clearAndFree();
        }

        var trans = std.ArrayList(*const processor.MA.Edge){};
        defer trans.deinit(self.gpa);
        var trans_set = std.AutoHashMap(*const processor.MA.Edge, void).init(self.gpa);
        defer trans_set.deinit();

        const RuleTail = struct {
            to: processor.State,
            new_top: processor.Symbol, // null for self-modifying rules
        };

        var rules_by_tail = std.AutoHashMap(RuleTail, std.ArrayList(*const processor.Rule)).init(self.gpa);
        defer {
            var it = rules_by_tail.iterator();
            while (it.next()) |e| {
                e.value_ptr.deinit(self.gpa);
            }
            rules_by_tail.deinit();
        }

        for (self.sm_pds.system.?.rules.items) |*rule| {
            switch (rule.rule) {
                .sm => |_| {
                    unreachable;
                    // const tail = RuleTail{
                    //     .to = r.to,
                    //     .new_top = r.top,
                    // };
                    // const gop = try rules_by_tail.getOrPut(tail);
                    // if (!gop.found_existing) {
                    //     gop.value_ptr.* = std.ArrayList(*const processor.Rule){};
                    // }
                    // try gop.value_ptr.append(self.gpa, rule);
                },
                .int => |r| {
                    if (r.new_top == null) continue;
                    const tail = RuleTail{
                        .to = r.to,
                        .new_top = r.new_top.?,
                    };
                    const gop = try rules_by_tail.getOrPut(tail);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = std.ArrayList(*const processor.Rule){};
                    }
                    try gop.value_ptr.append(self.gpa, &rule.rule);
                },
                .call => |r| {
                    const tail = RuleTail{
                        .to = r.to,
                        .new_top = r.new_top,
                    };
                    const gop = try rules_by_tail.getOrPut(tail);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = std.ArrayList(*const processor.Rule){};
                    }
                    try gop.value_ptr.append(self.gpa, &rule.rule);
                },
                .ret => {},
            }
        }

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        for (new_edges) |edge_ptr| {
            if (!trans_set.contains(edge_ptr)) {
                try trans.append(self.gpa, edge_ptr);
                try trans_set.put(edge_ptr, {});
            }
        }

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        for (self.edges.values()) |edge_ptr| {
            const edge = edge_ptr.*;
            const gop = try self.edges_by_trg.getOrPut(edge.to);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge_ptr, {});
        }

        while (trans.pop()) |edge| {
            if (!try self.pre_ma.addEdgePtr(edge)) {
                continue;
            }
            if (edge.from == .internal) continue;

            const hr_edges_opt = self.edges_by_trg.get(try self.addHead(Head{
                .state = edge.from.state,
                .top = edge.symbol,
            }));
            if (hr_edges_opt) |hr_edges| {
                for (hr_edges.keys()) |hr_edge| {
                    const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                        .from = .{ .state = hr_edge.from.state },
                        .symbol = hr_edge.from.top,
                        .to = edge.to,
                    });
                    if (!trans_set.contains(edge_ptr)) {
                        try trans.append(self.gpa, edge_ptr);
                        try trans_set.put(edge_ptr, {});
                    }
                }
            }

            if (rules_by_tail.get(.{ .to = edge.from.state, .new_top = edge.symbol })) |tail_rules| {
                for (tail_rules.items) |rule| {
                    switch (rule.*) {
                        .sm => {
                            unreachable;
                        },
                        .ret => unreachable,
                        .int => |r| {
                            if (r.new_tail == null) {
                                const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                                    .from = .{ .state = r.from },
                                    .symbol = r.top,
                                    .to = edge.to,
                                });
                                if (!trans_set.contains(edge_ptr)) {
                                    try trans.append(self.gpa, edge_ptr);
                                    try trans_set.put(edge_ptr, {});
                                }
                            } else {
                                const aux_edges_opt = self.pre_ma.edges_by_head.get(.{
                                    .from = edge.to,
                                    .symbol = r.new_tail.?,
                                });
                                if (aux_edges_opt) |aux_edges| {
                                    for (aux_edges.keys()) |edge_aux| {
                                        const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                                            .from = .{ .state = r.from },
                                            .symbol = r.top,
                                            .to = edge_aux.to,
                                        });
                                        if (!trans_set.contains(edge_ptr)) {
                                            try trans.append(self.gpa, edge_ptr);
                                            try trans_set.put(edge_ptr, {});
                                        }
                                    }
                                }
                            }
                        },
                        .call => |r| {
                            const aux_edges_opt = self.pre_ma.edges_by_head.get(.{
                                .from = edge.to,
                                .symbol = r.new_tail,
                            });
                            if (aux_edges_opt) |aux_edges| {
                                for (aux_edges.keys()) |edge_aux| {
                                    const edge_ptr = try self.pre_ma.storeEdge(processor.MA.Edge{
                                        .from = .{ .state = r.from },
                                        .symbol = r.top,
                                        .to = edge_aux.to,
                                    });
                                    if (!trans_set.contains(edge_ptr)) {
                                        try trans.append(self.gpa, edge_ptr);
                                        try trans_set.put(edge_ptr, {});
                                    }
                                }
                            }
                        },
                    }
                }
            }
        }
    }

    // Strongly connected component
    pub const SCC = struct {
        heads: []const *const Head,
    };

    // Tarjan algo
    pub fn findRepeatingHeads(self: *@This(), gpa: std.mem.Allocator) ![]SCC {
        defer {
            var it = self.edges_by_src.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }
            self.edges_by_src.clearAndFree();
        }

        var index: u32 = 0;

        var stack = std.ArrayList(*Head){};
        defer stack.deinit(gpa);

        var sccs = std.ArrayList(SCC){};
        defer sccs.deinit(gpa);

        for (self.edges.values()) |edge| {
            const src = edge.from;

            const gop = try self.edges_by_src.getOrPut(src);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge, {});
        }

        if (root.syscalls_enabled and root.state_initialized) {
            std.log.info("source map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        for (self.heads.values()) |head| {
            if (head.index == null) {
                try self.strongconnect(gpa, head, &stack, &index, &sccs);
            }
        }

        return try sccs.toOwnedSlice(gpa);
    }

    pub var global_printer: ?*Printer = null;

    fn strongconnect(self: *const @This(), gpa: std.mem.Allocator, head: *Head, stack: *std.ArrayList(*Head), index: *u32, sccs: *std.ArrayList(SCC)) !void {
        head.*.index = index.*;
        head.*.lowlink = index.*;
        index.* += 1;
        try stack.append(gpa, head);
        head.*.on_stack = true;

        const edges = self.edges_by_src.get(head);
        if (edges) |edge_list| {
            for (edge_list.keys()) |edge| {
                const to = edge.to;
                if (to.*.index == null) {
                    try self.strongconnect(gpa, @constCast(to), stack, index, sccs);
                    head.*.lowlink = @min(head.lowlink.?, to.lowlink.?);
                } else if (to.*.on_stack.?) {
                    head.*.lowlink = @min(head.lowlink.?, to.index.?);
                }
            }
        }

        if (head.*.lowlink.? == head.*.index.?) {
            if (root.syscalls_enabled and global_printer != null) {
                std.debug.print("Starting component from {f}\n", .{global_printer.?.node(head.*)});
            }

            var heads_count: usize = 0;
            if (stack.items.len > 0) {
                var i = stack.items.len - 1;
                while (i >= 0) : (i -= 1) {
                    heads_count += 1;
                    stack.items[i].*.on_stack = false;
                    if (stack.items[i] == head) break;
                }
            }
            const head_items = try gpa.dupe(*Head, stack.items[stack.items.len - heads_count ..]);
            errdefer gpa.free(head_items);
            stack.shrinkRetainingCapacity(stack.items.len - heads_count);

            var accepting = false;

            is_acc: for (head_items) |h1| {
                for (head_items) |h2| {
                    if (self.edges.contains(Edge{
                        .from = h1,
                        .to = h2,
                    })) {
                        accepting = true;
                        break :is_acc;
                    }
                }
            }

            if (accepting) {
                const scc = SCC{
                    .heads = head_items,
                };
                try sccs.append(gpa, scc);
            } else {
                gpa.free(head_items);
            }
        }
    }

    pub const Printer = struct {
        const Parent = @This();
        const Node = Head;

        gen: *processor.SM_PDS_Printer,
        pub fn init(gen: *processor.SM_PDS_Printer) Printer {
            return Printer{
                .gen = gen,
            };
        }

        pub const NodePrinter = struct {
            printer: *Parent,
            node: Node,

            pub fn format(
                self: @This(),
                writer: anytype,
            ) !void {
                try writer.print("[{f}, {f}]", .{ self.printer.gen.state(self.node.state), self.printer.gen.symbol(self.node.top) });
            }
        };

        pub fn node(self: *@This(), n: Node) NodePrinter {
            return .{
                .printer = self,
                .node = n,
            };
        }

        pub const EdgePrinter = struct {
            printer: *Parent,
            edge: Edge,

            pub fn format(
                self: @This(),
                writer: anytype,
            ) !void {
                try writer.print("{f} -->{s} {f}", .{ self.printer.node(self.edge.from.*), "", self.printer.node(self.edge.to.*) });
            }
        };

        pub fn edge(self: *@This(), e: Edge) EdgePrinter {
            return .{
                .printer = self,
                .edge = e,
            };
        }
    };
};

pub fn build_hr_pre(gpa: std.mem.Allocator, ma: *processor.MA, sccs: []const HeadReachabilityGraph.SCC) ![]*const processor.MA.Edge {
    var count: usize = 0;

    for (sccs) |scc| {
        for (scc.heads) |_| {
            count += 1;
        }
    }
    const res = try gpa.alloc(*const processor.MA.Edge, count);

    const acc_node = processor.MA.Node{
        .internal = 0,
    };

    var i: usize = 0;

    for (sccs) |scc| {
        for (scc.heads) |head| {
            res[i] = try ma.storeEdge(.{
                .from = .{ .state = head.state },
                .to = acc_node,
                .symbol = head.top,
            });
            i += 1;
        }
    }
    return res;
}

const parser = @import("parser.zig");
test "schwoon" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const gpa = std.testing.allocator;

    var proc = processor.SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(allocator, "tests/false-0.smpds");

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const pds = try processor.translate_to_naive(gpa, arena.allocator(), &proc, unprocessed_conf);

    var pds_proc = processor.SM_PDS_Processor.init(arena.allocator(), gpa);
    defer pds_proc.deinit();

    try pds_proc.process(pds.smpds, pds.init);
    // var pds_conf = try pds_proc.getInit(pds.init);
    // const ini = try proc.getInit(unprocessed_conf.init);

    var p_pre_ma = processor.MA.init(allocator, std.testing.allocator);
    defer p_pre_ma.deinit();

    var hr = HeadReachabilityGraph.init(allocator, std.testing.allocator, &p_pre_ma, &pds_proc);
    defer hr.deinit();

    try hr.constructSchwoon();

    const sccs = try hr.findRepeatingHeads(gpa);
    defer {
        for (sccs) |scc| {
            gpa.free(scc.heads);
        }
        gpa.free(sccs);
    }

    // for (sccs) |scc| {
    //     std.debug.print("{any}\n", .{scc.heads});
    // }
    const new_edges = try build_hr_pre(gpa, &p_pre_ma, sccs);
    defer gpa.free(new_edges);

    try hr.appendSchwoon(new_edges);

    var printer = try processor.SM_PDS_Printer.init(std.testing.allocator, &pds_proc);
    defer printer.deinit();
    // var it = p_pre_ma.edge_storage.keyIterator();

    // while (it.next()) |edge| {
    //     if (edge.to == .state) {
    //         std.debug.print("{f} -{f}-> {f}\n", .{ printer.state(edge.*.from.state), printer.symbol(edge.*.symbol), printer.state(edge.*.to.state) });
    //     } else {
    //         std.debug.print("{f} -{f}-> {d}\n", .{ printer.state(edge.*.from.state), printer.symbol(edge.*.symbol), edge.*.to.internal });
    //     }
    // }
}
