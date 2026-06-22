const parser = @import("parser.zig");
const processor = @import("processor.zig");

const gbuchi = @import("gbuchi.zig");
const naive_gbuchi = @import("naive_gbuchi.zig");
const ama = @import("ama.zig");
const naive_ama = @import("naive_ama.zig");
const hr = @import("head_reachability.zig");
const builtin = @import("builtin");
const std = @import("std");

pub const syscalls_enabled = builtin.target.os.tag != .freestanding;

const logger = if (syscalls_enabled)
    std.log
else
    struct {};

const time_struct = if (syscalls_enabled)
    std.time
else
    struct {};

var pytest: bool = false;
var naive: bool = false;
var bin: bool = false;
var input_filename: ?[]const u8 = null;

const CommandLineError = error{ InvalidArgument, FileNameMissing };

fn parse_args(args: [][:0]u8) !void {
    for (args[1..]) |arg| {
        if (arg[0] != '-') {
            if (input_filename != null) {
                std.log.err("Two filenames provided: {s} and {s}\n", .{ input_filename.?, arg });
                return CommandLineError.InvalidArgument;
            }
            input_filename = arg;
            continue;
        }
        var strip_ind: usize = 0;
        for (arg, 0..) |b, i| {
            if (b != '-') {
                strip_ind = i;
                break;
            }
        }
        const arg_stripped = arg[strip_ind..];
        if (std.mem.eql(u8, arg_stripped, "pytest")) {
            pytest = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "naive")) {
            naive = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "bin")) {
            bin = true;
            continue;
        }
        std.log.err("Unknown argument {s}\n", .{arg_stripped});
        return CommandLineError.InvalidArgument;
    }
}

const RlimitError = error{FailedToSetRlimit};

pub const GlobalState = struct {
    timer: *std.time.Timer,
    errors: []const u8,

    arena: *std.heap.ArenaAllocator,
    progress: ?std.Progress.Node,
};

pub var state_initialized = false;
pub var state: GlobalState = undefined;
var timerv: std.time.Timer = undefined;

pub fn main() !void {
    const limit = std.os.linux.rlimit{
        .cur = 8 * 1024 * 1024 * 1024,
        .max = 9 * 1024 * 1024 * 1024,
    };
    const rlimit_res = std.os.linux.setrlimit(.AS, &limit);
    if (rlimit_res != 0) {
        return RlimitError.FailedToSetRlimit;
    }

    timerv = try std.time.Timer.start();
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    state_initialized = true;
    state = GlobalState{
        .timer = &timerv,
        .arena = &arena,
        .errors = &.{},
        .progress = null, //std.Progress.start(.{ .root_name = "model checking" }),
    };

    var gpa = std.heap.GeneralPurposeAllocator(.{}).init;

    const args = try std.process.argsAlloc(arena.allocator());
    defer std.process.argsFree(arena.allocator(), args);

    try parse_args(args);

    if (input_filename == null) {
        std.log.err("Provide a filename\n", .{});
        return CommandLineError.FileNameMissing;
    }

    var result: bool = undefined;
    if (pytest) {
        if (naive) {
            result = bcaret_model_check_pytest_naive(gpa.allocator(), arena.allocator(), input_filename.?) catch |e| {
                print_errors(e);
                return e;
            };
        } else {
            result = bcaret_model_check_pytest(gpa.allocator(), arena.allocator(), input_filename.?) catch |e| {
                print_errors(e);
                return e;
            };
        }
    } else if (bin) {
        result = bcaret_model_check_bin(gpa.allocator(), arena.allocator(), input_filename.?) catch |e| {
            print_errors(e);
            return e;
        };
    } else {
        result = bcaret_model_check_smpds_file(gpa.allocator(), arena.allocator(), input_filename.?) catch |e| {
            print_errors(e);
            return e;
        };
    }

    var stdout_buffer: [1024]u8 = undefined;
    var stdout_writer = std.fs.File.stdout().writer(&stdout_buffer);
    defer stdout_writer.interface.flush() catch @panic("oops");
    const stdout = &stdout_writer.interface;

    try stdout.print("{s}\n", .{if (result) "True" else "False"});

    if (pytest) {
        const f_time: f64 = @floatFromInt(timerv.lap());
        const f_mem: f64 = @floatFromInt(arena.queryCapacity());
        try stdout.print("Memory used: {d:.3} KB\n", .{f_mem / 1024});
        try stdout.print("Time took: {d:.3}s\n", .{f_time / 1000000000});
    }
    try stdout.flush();
}

pub fn print_errors(e: anyerror) void {
    std.log.err("{}", .{e});

    const f_time: f64 = @floatFromInt(state.timer.read());
    const f_mem: f64 = @floatFromInt(state.arena.queryCapacity());
    std.log.err("Memory used: {d:.3} KB", .{f_mem / 1024});
    std.log.err("Time took: {d:.3}s", .{f_time / 1000000000});
}

pub fn parse_smpds_file(allocator: std.mem.Allocator, filename: []const u8) !parser.ParsedSMPDS {
    var file = parser.SmpdsFile.open(allocator, filename);
    const unprocessed_conf = try file.parse();
    return unprocessed_conf;
}

pub fn recordTime(comptime str: []const u8, args: anytype) void {
    if (syscalls_enabled and state_initialized) {
        std.log.info(str, args);
        std.log.info("{d:.3}s", .{
            @as(f64, @floatFromInt(state.timer.read())) / 1000000000,
        });
        std.log.info("^^^", .{});
    }
}

pub fn bcaret_model_check(
    gpa: std.mem.Allocator,
    arena: std.mem.Allocator,
    proc: *processor.SM_PDS_Processor,
    conf: processor.Conf,
    formula: processor.BranchCaret.Formula,
    lambda: processor.LabellingFunction,
) !bool {
    if (syscalls_enabled and state_initialized) {
        std.log.info("P PRe MA Start: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }

    _ = .{ gpa, arena, proc, conf, formula, lambda };
    const closure = try formula.get_closure(gpa);
    defer {
        for (closure) |f| {
            f.deinit(gpa);
        }
        gpa.free(closure);
    }

    var p_pre_ma = processor.MA.init(arena, gpa);
    defer p_pre_ma.deinit();

    if (syscalls_enabled and state_initialized) {
        std.log.info("Buchi Start: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }
    var gbpds = gbuchi.SM_GBPDS_Processor.init(gpa, arena);
    defer gbpds.deinit();

    const ginit = gbuchi.State{ .control = .{ .control_point = .{ .state = conf.state }, .label = .{ .formula = formula } } };

    try gbpds.construct_optimized(proc, closure, lambda, ginit, conf.phase, &p_pre_ma);

    if (syscalls_enabled and state_initialized) {
        std.log.info("GBPDS constructed ({} rules taking {d:.3} MB): {d:.3}s", .{
            gbpds.rule_set.count(),
            @as(f64, @floatFromInt(gbpds.rule_set.capacity() * @sizeOf(gbuchi.Rule))) / (1024 * 1024),
            @as(f64, @floatFromInt(state.timer.read())) / 1000000000,
        });
    }

    var ama_solver = try ama.AMASolver.init(arena, gpa, &gbpds, &lambda);

    defer ama_solver.deinit();

    try ama_solver.construct(null);

    // var printer = try gbuchi.SM_GBPDS_Printer.init(gpa, proc);
    // defer printer.deinit();
    // var ama_printer = ama.AMAPrettyPrinter{
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

    const ama_word = try gpa.alloc(ama.BuchiAMA.Symbol, conf.stack.len + 1);
    defer gpa.free(ama_word);

    for (ama_word[0..conf.stack.len], conf.stack) |*aw, st| {
        aw.* = .{ .symbol = .{ .standard = st } };
    }
    ama_word[conf.stack.len] = .{ .symbol = .{ .standard = try proc.process_symbol("#") } };

    const res = try ama_solver.get_paths(arena, try ama_solver.get_node_name(.{ .control_point = ginit, .iter = ama_solver.final_iter, .phase = conf.phase }), ama_word, 0);

    if (syscalls_enabled and state_initialized) {
        std.log.info("Finish: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }

    var result = false;
    for (res.items) |inp| {
        if (inp.succ.items.count() == 1 and inp.succ.items.keys()[0] == ama_solver.accept_node) {
            result = true;
        }
    }
    return result;
}
// Different functions for model checking files depending on the input format:
//
pub fn bcaret_model_check_unproc(gpa: std.mem.Allocator, arena: std.mem.Allocator, unprocessed_conf: parser.ParsedSMPDS, lfunc: processor.LabellingFunction.Labeller) !bool {
    var proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer proc.deinit();

    const unprocessed = unprocessed_conf.smpds;
    if (syscalls_enabled and state_initialized) {
        std.log.info("Start: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }
    try proc.process(unprocessed, unprocessed_conf.init);
    const conf = try proc.getInit(unprocessed_conf.init);

    const formula = try processor.processCaret(arena, unprocessed_conf.branchcaret.formula);

    var lambda = try processor.LabellingFunction.init(gpa, &proc, formula, lfunc, unprocessed_conf.branchcaret.valuations);
    defer lambda.deinit();

    if (syscalls_enabled and state_initialized) {
        std.log.info("Preprocess finished ({} rules in SM-PDS): {d:.3}s", .{
            proc.system.?.rules.items.len,
            @as(f64, @floatFromInt(state.timer.read())) / 1000000000,
        });
    }
    // return if (pytest)
    //     try caret_model_check_no_opt(gpa, arena, &proc, conf, formula, lambda)
    // else
    return try bcaret_model_check(gpa, arena, &proc, conf, formula, lambda);
}

pub fn bcaret_model_check_smpds_file(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    var file = parser.SmpdsFile.open(arena, filename);
    const unprocessed_conf = try file.parse();

    return bcaret_model_check_unproc(gpa, arena, unprocessed_conf, processor.LabellingFunction.strict);
}

pub fn bcaret_model_check_bin(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    const unprocessed_conf = try parser.parseJsonFromPython(gpa, arena, filename);

    return bcaret_model_check_unproc(gpa, arena, unprocessed_conf, processor.LabellingFunction.substr);
}

pub fn bcaret_model_check_pytest(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    const unprocessed_conf = try parser.parseJsonFromPython(gpa, arena, filename);

    return bcaret_model_check_unproc(gpa, arena, unprocessed_conf, processor.LabellingFunction.strict);
}

pub fn bcaret_model_check_smpds_naive(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    var timer = try std.time.Timer.start();

    var file = parser.SmpdsFile.open(arena, filename);
    const unprocessed_conf = try file.parse();
    var proc = processor.SM_PDS_Processor.init(arena, gpa);

    defer proc.deinit();

    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    _ = try proc.getInit(unprocessed_conf.init);

    _ = timer.lap();

    const pds = try processor.translate_to_naive(gpa, arena, &proc, unprocessed_conf);
    var pds_proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer pds_proc.deinit();

    // std.debug.print("Naive: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});

    try pds_proc.process(pds.smpds, pds.init);
    const pds_conf = try pds_proc.getInit(pds.init);

    var p_pre_ma = processor.MA.init(arena, gpa);
    defer p_pre_ma.deinit();
    var hrg = hr.HeadReachabilityGraph.init(arena, gpa, &p_pre_ma, &pds_proc);
    defer hrg.deinit();

    try hrg.constructSchwoon();

    const sccs = try hrg.findRepeatingHeads(gpa);
    defer {
        for (sccs) |scc| {
            gpa.free(scc.heads);
        }
        gpa.free(sccs);
    }

    const new_edges = try hr.build_hr_pre(gpa, &p_pre_ma, sccs);
    defer gpa.free(new_edges);

    try hrg.appendSchwoon(new_edges);

    if (syscalls_enabled and state_initialized) {
        std.log.info("Naive Buchi Start: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }
    var gbpds = naive_gbuchi.SM_GBPDS_Processor.init(gpa, arena, &p_pre_ma);
    defer gbpds.deinit();

    const formula = try processor.processCaret(arena, pds.branchcaret.formula);

    var lambda = try processor.LabellingFunction.init(gpa, &pds_proc, formula, processor.LabellingFunction.naive, pds.branchcaret.valuations);
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

    try gbpds.construct_optimized(&pds_proc, closure, lambda, &.{ginit});

    if (syscalls_enabled and state_initialized) {
        std.log.info("GBPDS constructed ({} rules taking {d:.3} MB): {d:.3}s", .{
            gbpds.rule_set.count(),
            @as(f64, @floatFromInt(gbpds.rule_set.capacity() * @sizeOf(gbuchi.Rule))) / (1024 * 1024),
            @as(f64, @floatFromInt(state.timer.read())) / 1000000000,
        });
    }

    var ama_solver = try naive_ama.AMASolver.init(arena, gpa, &gbpds, &lambda);

    defer ama_solver.deinit();

    try ama_solver.construct(null);

    const ama_word = try gpa.alloc(naive_ama.BuchiAMA.Symbol, pds_conf.stack.len + 1);
    defer gpa.free(ama_word);

    for (ama_word[0..pds_conf.stack.len], pds_conf.stack) |*aw, st| {
        aw.* = .{ .symbol = .{ .symbol = st } };
    }
    ama_word[pds_conf.stack.len] = .{ .symbol = .{ .symbol = try pds_proc.process_symbol("#") } };

    const res = try ama_solver.get_paths(arena, try ama_solver.get_node_name(.{ .control_point = ginit, .iter = ama_solver.final_iter }), ama_word, 0);

    if (syscalls_enabled and state_initialized) {
        std.log.info("Finish: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }

    var result = false;
    for (res.items) |inp| {
        if (inp.succ.items.count() == 1 and inp.succ.items.keys()[0] == ama_solver.accept_node) {
            result = true;
        }
    }
    return result;
}

pub fn bcaret_model_check_pytest_naive(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    var timer = try std.time.Timer.start();

    const unprocessed_conf = try parser.parseJsonFromPython(gpa, arena, filename);

    var proc = processor.SM_PDS_Processor.init(arena, gpa);

    defer proc.deinit();

    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    _ = try proc.getInit(unprocessed_conf.init);

    _ = timer.lap();

    const pds = try processor.translate_to_naive(gpa, arena, &proc, unprocessed_conf);
    var pds_proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer pds_proc.deinit();

    // std.debug.print("Naive: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});

    try pds_proc.process(pds.smpds, pds.init);
    const pds_conf = try pds_proc.getInit(pds.init);

    var p_pre_ma = processor.MA.init(arena, gpa);
    defer p_pre_ma.deinit();
    var hrg = hr.HeadReachabilityGraph.init(arena, gpa, &p_pre_ma, &pds_proc);
    defer hrg.deinit();

    try hrg.constructSchwoon();

    const sccs = try hrg.findRepeatingHeads(gpa);
    defer {
        for (sccs) |scc| {
            gpa.free(scc.heads);
        }
        gpa.free(sccs);
    }

    const new_edges = try hr.build_hr_pre(gpa, &p_pre_ma, sccs);
    defer gpa.free(new_edges);

    try hrg.appendSchwoon(new_edges);

    if (syscalls_enabled and state_initialized) {
        std.log.info("Naive Buchi Start: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }
    var gbpds = naive_gbuchi.SM_GBPDS_Processor.init(gpa, arena, &p_pre_ma);
    defer gbpds.deinit();

    const formula = try processor.processCaret(arena, pds.branchcaret.formula);

    var lambda = try processor.LabellingFunction.init(gpa, &pds_proc, formula, processor.LabellingFunction.naive, pds.branchcaret.valuations);
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

    try gbpds.construct_optimized(&pds_proc, closure, lambda, &.{ginit});

    if (syscalls_enabled and state_initialized) {
        std.log.info("GBPDS constructed ({} rules taking {d:.3} MB): {d:.3}s", .{
            gbpds.rule_set.count(),
            @as(f64, @floatFromInt(gbpds.rule_set.capacity() * @sizeOf(gbuchi.Rule))) / (1024 * 1024),
            @as(f64, @floatFromInt(state.timer.read())) / 1000000000,
        });
    }

    var ama_solver = try naive_ama.AMASolver.init(arena, gpa, &gbpds, &lambda);

    defer ama_solver.deinit();

    try ama_solver.construct(null);

    const ama_word = try gpa.alloc(naive_ama.BuchiAMA.Symbol, pds_conf.stack.len + 1);
    defer gpa.free(ama_word);

    for (ama_word[0..pds_conf.stack.len], pds_conf.stack) |*aw, st| {
        aw.* = .{ .symbol = .{ .symbol = st } };
    }
    ama_word[pds_conf.stack.len] = .{ .symbol = .{ .symbol = try pds_proc.process_symbol("#") } };

    const res = try ama_solver.get_paths(arena, try ama_solver.get_node_name(.{ .control_point = ginit, .iter = ama_solver.final_iter }), ama_word, 0);

    if (syscalls_enabled and state_initialized) {
        std.log.info("Finish: {d:.3}s", .{@as(f64, @floatFromInt(state.timer.read())) / 1000000000});
    }

    var result = false;
    for (res.items) |inp| {
        if (inp.succ.items.count() == 1 and inp.succ.items.keys()[0] == ama_solver.accept_node) {
            result = true;
        }
    }
    return result;
}

test "naive" {
    if (debug) {
        try std.testing.expect(true);
        return;
    }
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const cwd = std.fs.cwd();
    const test_dir = try cwd.openDir("tests", .{
        .iterate = true,
    });

    var test_file_iter = test_dir.iterate();
    while (try test_file_iter.next()) |file| {
        if (file.kind == .file and std.mem.endsWith(u8, file.name, ".smpds")) {
            // std.debug.print("testing {s}\n", .{file.name});
            const name = file.name;

            const res = bcaret_model_check_smpds_naive(gpa, arena.allocator(), try test_dir.realpathAlloc(arena.allocator(), file.name)) catch |err| {
                std.debug.print("Failed {s}\n", .{name});
                return err;
            };

            std.testing.expectEqual(std.mem.startsWith(u8, name, "true"), res) catch |err| {
                std.debug.print("Failed {s}\n", .{name});
                return err;
            };
        }
    }
}

test "whole" {
    if (debug) {
        try std.testing.expect(true);
        return;
    }
    const gpa = std.testing.allocator;

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const cwd = std.fs.cwd();
    const test_dir = try cwd.openDir("tests", .{
        .iterate = true,
    });

    var test_file_iter = test_dir.iterate();
    while (try test_file_iter.next()) |file| {
        if (file.kind == .file and std.mem.endsWith(u8, file.name, ".smpds")) {
            // std.debug.print("testing {s}\n", .{file.name});
            const name = file.name;

            const res = bcaret_model_check_smpds_file(gpa, arena.allocator(), try test_dir.realpathAlloc(arena.allocator(), file.name)) catch |err| {
                std.debug.print("Failed {s}\n", .{name});
                return err;
            };

            std.testing.expectEqual(std.mem.startsWith(u8, name, "true"), res) catch |err| {
                std.debug.print("Failed {s}\n", .{name});
                return err;
            };
        }
    }
}

test "dependencies" {
    _ = parser.SM_PDS;
    _ = processor.SM_PDS_Processor;
    _ = gbuchi.SM_GBPDS_Processor;
    _ = ama.AMASolver;
    _ = naive_ama.AMASolver;
    _ = naive_gbuchi.SM_GBPDS_Processor;
    _ = hr.HeadReachabilityGraph;
}

// const debug = true;
const debug = false;
test "debug" {
    if (true or !debug) {
        try std.testing.expect(true);
        return;
    }
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var proc = processor.SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(allocator, "tests/true-11.smpds");

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const ini = try proc.getInit(unprocessed_conf.init);

    var p_pre_ma = processor.MA.init(allocator, std.testing.allocator);
    defer p_pre_ma.deinit();

    var gbpds = gbuchi.SM_GBPDS_Processor.init(std.testing.allocator, allocator);
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
    var ginits = std.ArrayList(gbuchi.State){};
    defer ginits.deinit(allocator);

    const ginit = gbuchi.State{ .control = .{ .control_point = .{ .state = ini.state }, .label = .{ .formula = formula } } };
    try ginits.append(allocator, gbuchi.State{ .control = .{ .control_point = .{ .state = ini.state }, .label = .{ .formula = formula } } });

    try gbpds.construct_optimized(&proc, closure, lambda, ginits.items, &p_pre_ma);

    var printer = try gbuchi.SM_GBPDS_Printer.init(std.testing.allocator, &proc);
    defer printer.deinit();

    for (gbpds.rule_array.items) |rule| {
        std.debug.print("{f}\n", .{printer.rule(rule)});
    }

    var ama_solver = try ama.AMASolver.init(arena.allocator(), std.testing.allocator, &gbpds, &lambda);

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

    const ama_word = try std.testing.allocator.alloc(ama.BuchiAMA.Symbol, ini.stack.len + 1);
    defer std.testing.allocator.free(ama_word);
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
