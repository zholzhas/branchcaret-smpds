const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});

    const optimize = b.standardOptimizeOption(.{});

    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    const exe_mod = b.createModule(.{
        .root_source_file = if (target.result.os.tag == .freestanding) b.path("src/wasm_module.zig") else b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    exe_mod.addImport("bcaret_mc_smpds_lib", lib_mod);

    if (target.result.os.tag == .freestanding) {
        exe_mod.export_symbol_names = &.{ "read_smpds", "alloc", "free" };
    }
    const lib = b.addLibrary(.{
        .linkage = .static,
        .name = "bcaret_mc_smpds",
        .root_module = lib_mod,
    });
    b.installArtifact(lib);

    const exe = b.addExecutable(.{
        .name = "bcaret_mc_smpds",
        .root_module = exe_mod,
    });

    if (target.result.os.tag == .freestanding) {
        exe.entry = .disabled;
        exe.import_symbols = true;
        exe.export_table = true;
    }

    const mecha = b.dependency("mecha", .{});
    exe.root_module.addImport("mecha", mecha.module("mecha"));
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);

    run_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        run_cmd.addArgs(args);
    }
    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);

    const lib_unit_tests = b.addTest(.{
        .root_module = lib_mod,
    });

    const run_lib_unit_tests = b.addRunArtifact(lib_unit_tests);
    const exe_unit_tests = b.addTest(.{
        .root_module = exe_mod,
    });

    const run_exe_unit_tests = b.addRunArtifact(exe_unit_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_lib_unit_tests.step);
    test_step.dependOn(&run_exe_unit_tests.step);

    const debug_mod = b.createModule(.{
        .root_source_file = b.path("src/debug.zig"),
        .target = target,
        .optimize = optimize,
    });
    debug_mod.addImport("bcaret_mc_smpds_lib", lib_mod);
    const debug_exe = b.addExecutable(.{
        .name = "bcaret_mc_smpds_debug",
        .root_module = debug_mod,
    });
    debug_exe.root_module.addImport("mecha", mecha.module("mecha"));

    const run_debug = b.addRunArtifact(debug_exe);

    const debug_step = b.step("debug", "Debug from debug.zig");
    debug_step.dependOn(&run_debug.step);
}
