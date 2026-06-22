const parser = @import("parser.zig");
const processor = @import("processor.zig");

const gbuchi = @import("gbuchi.zig");
const naive_gbuchi = @import("naive_gbuchi.zig");
const ama = @import("ama.zig");
const naive_ama = @import("naive_ama.zig");
const hr = @import("head_reachability.zig");
const builtin = @import("builtin");
const std = @import("std");

const root = @import("main.zig");

pub fn main() !void {
    const file = "tests/true-11.smpds";
    try smpds(file);
    // try naive(file);
}

pub fn smpds(filename: []const u8) !void {
    var debug_alloc = std.heap.DebugAllocator(.{}).init;
    defer {
        _ = debug_alloc.detectLeaks();
        _ = debug_alloc.deinit();
    }
    const gpa = debug_alloc.allocator();

    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const allocator = arena.allocator();
    // const ress = try root.bcaret_model_check_smpds_file(gpa, allocator, filename);
    // if (ress) {
    //     std.debug.print("True\n", .{});
    // } else {
    //     std.debug.print("False\n", .{});
    // }
    // if (true) return;

    var proc = processor.SM_PDS_Processor.init(allocator, gpa);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(allocator, filename);
    const unprocessed_conf = try file.parse();

    // const unprocessed_conf = try parser.parseJsonFromPython(gpa, allocator, filename);

    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const ini = try proc.getInit(unprocessed_conf.init);

    var p_pre_ma = processor.MA.init(allocator, gpa);
    defer p_pre_ma.deinit();

    var gbpds = gbuchi.SM_GBPDS_Processor.init(gpa, allocator);
    defer gbpds.deinit();

    const formula = try processor.processCaret(allocator, unprocessed_conf.branchcaret.formula);

    const closure = try formula.get_closure(gpa);
    defer {
        for (closure) |f| {
            f.deinit(gpa);
        }
        gpa.free(closure);
    }

    var lambda = try processor.LabellingFunction.init(gpa, &proc, formula, processor.LabellingFunction.strict, unprocessed_conf.branchcaret.valuations);
    defer lambda.deinit();
    var ginits = std.ArrayList(gbuchi.State){};
    defer ginits.deinit(allocator);

    const ginit = gbuchi.State{ .control = .{ .control_point = .{ .state = ini.state }, .label = .{ .formula = formula } } };
    try ginits.append(allocator, gbuchi.State{ .control = .{ .control_point = .{ .state = ini.state }, .label = .{ .formula = formula } } });

    try gbpds.construct_optimized(&proc, closure, lambda, ginit, ini.phase, &p_pre_ma);

    var printer = try gbuchi.SM_GBPDS_Printer.init(gpa, &proc);
    defer printer.deinit();

    for (gbpds.rule_array.items) |rule| {
        std.debug.print("{f}\n", .{printer.rule(rule)});
    }

    var ama_solver = try ama.AMASolver.init(arena.allocator(), gpa, &gbpds, &lambda);

    defer ama_solver.deinit();

    try ama_solver.construct(null);

    var ama_printer = ama.AMAPrettyPrinter{
        .buchi_printer = &printer,
        .solver = &ama_solver,
    };
    std.debug.print("Edges:\n", .{});
    var it = ama_solver.ama.edges.valueIterator();
    while (it.next()) |edge_ptr_ptr| {
        // if (solver.accept_node == edge_node.data.from or ama_printer.solver.init_nodes.get(edge_node.data.from).?.iter == solver.final_iter)
        std.debug.print("[{*}]: {f}\n", .{ edge_ptr_ptr.*, ama_printer.edge(edge_ptr_ptr.*.*) });
    }
    std.debug.print("\n", .{});

    const ama_word = try gpa.alloc(ama.BuchiAMA.Symbol, ini.stack.len + 1);
    defer gpa.free(ama_word);
    for (ama_word[0..ini.stack.len], ini.stack) |*aw, st| {
        aw.* = .{ .symbol = .{ .standard = st } };
    }
    ama_word[ini.stack.len] = .{ .symbol = .{ .standard = try proc.process_symbol("#") } };
    const res = try ama_solver.get_paths(arena.allocator(), try ama_solver.get_node_name(.{ .control_point = ginit, .iter = ama_solver.final_iter, .phase = ini.phase }), ama_word, 0);

    var result = false;
    for (res.items) |inp| {
        if (inp.succ.items.count() == 1 and inp.succ.items.keys()[0] == ama_solver.accept_node) {
            result = true;
        }
    }
    if (result) {
        std.debug.print("True\n", .{});
    } else {
        std.debug.print("False\n", .{});
    }
}

pub fn naive(filename: []const u8) !void {
    var debug_alloc = std.heap.DebugAllocator(.{}).init;
    defer {
        _ = debug_alloc.detectLeaks();
        _ = debug_alloc.deinit();
    }
    const gpa = debug_alloc.allocator();

    var arena_alloc = std.heap.ArenaAllocator.init(gpa);
    defer arena_alloc.deinit();
    const arena = arena_alloc.allocator();

    var file = parser.SmpdsFile.open(arena, filename);
    const unprocessed_conf = try file.parse();

    // const unprocessed_conf = try parser.parseJsonFromPython(gpa, arena, filename);

    var _proc = processor.SM_PDS_Processor.init(arena, gpa);

    defer _proc.deinit();

    const unprocessed = unprocessed_conf.smpds;
    try _proc.process(unprocessed, unprocessed_conf.init);
    _ = try _proc.getInit(unprocessed_conf.init);

    const pds = try processor.translate_to_naive(gpa, arena, &_proc, unprocessed_conf);
    var proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer proc.deinit();

    // std.debug.print("Naive: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});

    try proc.process(pds.smpds, pds.init);
    const pds_conf = try proc.getInit(pds.init);

    var p_pre_ma = processor.MA.init(arena, gpa);
    defer p_pre_ma.deinit();
    var hrg = hr.HeadReachabilityGraph.init(arena, gpa, &p_pre_ma, &proc);
    defer hrg.deinit();

    try hrg.constructSchwoon();

    const sccs = try hrg.findRepeatingHeads(gpa);
    defer {
        for (sccs) |scc| {
            gpa.free(scc.heads);
        }
        gpa.free(sccs);
    }
    var proc_printer = try processor.SM_PDS_Printer.init(gpa, &proc);
    defer proc_printer.deinit();
    std.debug.print("{} SCCs\n", .{sccs.len});
    for (sccs, 0..) |scc, i| {
        std.debug.print("{}: \n", .{i});
        for (scc.heads) |head| {
            std.debug.print("<{f}, {f}>, ", .{ proc_printer.state(head.state), proc_printer.symbol(head.top) });
        }
    }
    std.debug.print("\n", .{});

    const new_edges = try hr.build_hr_pre(gpa, &p_pre_ma, sccs);
    defer gpa.free(new_edges);

    try hrg.appendSchwoon(new_edges);

    var gbpds = naive_gbuchi.SM_GBPDS_Processor.init(gpa, arena, &p_pre_ma);
    defer gbpds.deinit();

    const formula = try processor.processCaret(arena, pds.branchcaret.formula);

    var lambda = try processor.LabellingFunction.init(gpa, &proc, formula, processor.LabellingFunction.naive, pds.branchcaret.valuations);
    defer lambda.deinit();

    // const res = try bcaret_model_check(gpa, arena, &pds_proc, pds_conf, formula, lambda);
    const closure = try formula.get_closure(gpa);
    defer {
        for (closure) |f| {
            f.deinit(gpa);
        }
        gpa.free(closure);
    }

    const ginit = naive_gbuchi.State{ .control = .{ .control_point = .{ .state = pds_conf.state }, .label = .{ .formula = formula } } };

    try gbpds.construct_optimized(&proc, closure, lambda, &.{ginit});

    var printer = try naive_gbuchi.SM_GBPDS_Printer.init(gpa, &proc);
    defer printer.deinit();
    for (gbpds.rule_array.items) |rule| {
        std.debug.print("{f}\n", .{printer.rule(rule)});
    }

    var ama_solver = try naive_ama.AMASolver.init(arena, gpa, &gbpds, &lambda);

    defer ama_solver.deinit();

    var ama_printer = naive_ama.AMAPrettyPrinter{
        .buchi_printer = &printer,
        .solver = &ama_solver,
    };
    try ama_solver.construct(null);
    std.debug.print("Edges:\n", .{});
    var it = ama_solver.ama.edges.valueIterator();
    while (it.next()) |edge_ptr_ptr| {
        // if (solver.accept_node == edge_node.data.from or ama_printer.solver.init_nodes.get(edge_node.data.from).?.iter == solver.final_iter)
        std.debug.print("[{*}]: {f}\n", .{ edge_ptr_ptr.*, ama_printer.edge(edge_ptr_ptr.*.*) });
    }
    std.debug.print("\n", .{});

    const ama_word = try gpa.alloc(naive_ama.BuchiAMA.Symbol, pds_conf.stack.len + 1);
    defer gpa.free(ama_word);

    for (ama_word[0..pds_conf.stack.len], pds_conf.stack) |*aw, st| {
        aw.* = .{ .symbol = .{ .symbol = st } };
    }
    ama_word[pds_conf.stack.len] = .{ .symbol = .{ .symbol = try proc.process_symbol("#") } };

    const res = try ama_solver.get_paths(arena, try ama_solver.get_node_name(.{ .control_point = ginit, .iter = ama_solver.final_iter }), ama_word, 0);

    var result = false;
    for (res.items) |inp| {
        if (inp.succ.items.count() == 1 and inp.succ.items.keys()[0] == ama_solver.accept_node) {
            result = true;
        }
    }
    if (result) {
        std.debug.print("True\n", .{});
    } else {
        std.debug.print("False\n", .{});
    }
}
