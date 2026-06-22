const std = @import("std");
const mecha = @import("mecha");

pub const RuleType = enum { internal, sm, call, ret };

pub const Conf = struct {
    state: []const u8,
    stack: []const []const u8,
    phase: []const []const u8,

    pub fn format(
        self: @This(),
        writer: *std.io.Writer,
    ) std.io.Writer.Error!void {
        try writer.print("{s} ", .{self.state});
        for (self.stack) |sym| {
            try writer.print("{s} ", .{sym});
        }
        try writer.print("# ", .{});
        for (self.phase) |sym| {
            try writer.print("{s} ", .{sym});
        }
    }
};

pub const Rule = struct {
    name: []const u8,
    typ: RuleType,
    from: []const u8,
    top: ?[]const u8 = null,
    to: []const u8,
    new_top: ?[]const u8 = null,
    new_tail: ?[]const u8 = null,
    sm_l: ?[]const []const u8 = null,
    sm_r: ?[]const []const u8 = null,

    pub fn format(
        self: @This(),
        writer: *std.io.Writer,
    ) !void {
        return switch (self.typ) {
            RuleType.internal => writer.print("{s}: {s} {s} \\--> {s} {s} {s}", .{ self.name, self.from, self.top.?, self.to, self.new_top orelse "-", self.new_tail orelse "-" }),
            RuleType.call => writer.print("{s}: {s} {s} \\-call-> {s} {s} {s}", .{ self.name, self.from, self.top.?, self.to, self.new_top.?, self.new_tail.? }),
            RuleType.ret => writer.print("{s}: {s} {s} \\-ret-> {s}", .{ self.name, self.from, self.top.?, self.to }),
            RuleType.sm => {
                try writer.print("{s}: {s} \\--(", .{ self.name, self.from });
                for (self.sm_l.?, 0..) |r, i| {
                    if (i > 0) {
                        try writer.print(", ", .{});
                    }
                    try writer.print("{s}", .{r});
                }
                try writer.print(")-/-(", .{});
                for (self.sm_r.?, 0..) |r, i| {
                    if (i > 0) {
                        try writer.print(", ", .{});
                    }
                    try writer.print("{s}", .{r});
                }
                try writer.print(")--> {s}", .{self.to});
            },
        };
    }
};

pub const SM_PDS = struct {
    states: [][]const u8,
    alphabet: [][]const u8,
    rules: []const Rule,
};

const JsonError = error{
    InvalidSMRule,
};

const ParsedJson = struct {
    system: ParsedSMPDS,
    labels: std.StringArrayHashMap([]const []const u8),
};

pub fn parseJsonFromPython(_: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !ParsedSMPDS {
    var file = try std.fs.cwd().openFile(filename, .{});
    defer file.close();

    var buf: [1000]u8 = undefined;
    var freader = file.reader(&buf);
    var reader = std.json.Reader.init(arena, &freader.interface);

    const val = try std.json.parseFromTokenSourceLeaky(std.json.Value, arena, &reader, .{});

    const smpds = val.array.items[0];
    var states = try arena.alloc([]const u8, smpds.array.items[0].array.items.len);

    for (smpds.array.items[0].array.items, 0..) |s, j| {
        states[j] = try arena.dupe(u8, s.string);
    }

    var alphabet = try arena.alloc([]const u8, smpds.array.items[1].array.items.len);
    for (smpds.array.items[1].array.items, 0..) |s, j| {
        alphabet[j] = try arena.dupe(u8, s.string);
    }

    var rules = try arena.alloc(Rule, smpds.array.items[2].object.count() + smpds.array.items[3].object.count());

    for (smpds.array.items[2].object.keys(), 0..) |name, j| {
        const r = smpds.array.items[2].object.get(name).?.array;

        if (r.items.len != 5) {
            std.log.err("Invalid JSON provided: Rule {s} does not contains 5 elements (p.1 g.2 -> p.3 g.4 label.5)", .{name});
            return JsonError.InvalidSMRule;
        }

        var new_top: ?[]const u8 = undefined;
        var new_tail: ?[]const u8 = undefined;
        if (r.items[3].string.len == 0) {
            new_top = null;
            new_tail = null;
        } else {
            if (std.mem.indexOf(u8, r.items[3].string, " ")) |ind| {
                new_top = try arena.dupe(u8, r.items[3].string[0..ind]);
                new_tail = try arena.dupe(u8, r.items[3].string[ind + 1 ..]);
            } else {
                new_top = try arena.dupe(u8, r.items[3].string);
                new_tail = null;
            }
        }

        rules[j] = Rule{
            .name = try arena.dupe(u8, name),
            .from = try arena.dupe(u8, r.items[0].string),
            .to = try arena.dupe(u8, r.items[2].string),
            .top = try arena.dupe(u8, r.items[1].string),
            .new_top = new_top,
            .new_tail = new_tail,
            .typ = if (std.mem.eql(u8, r.items[4].string, "call")) RuleType.call else if (std.mem.eql(u8, r.items[4].string, "int")) RuleType.internal else if (std.mem.eql(u8, r.items[4].string, "ret")) RuleType.ret else {
                std.log.err("Invalid JSON provided: Rule {s} is labelled with unknown label '{s}'", .{ name, r.items[4].string });
                return JsonError.InvalidSMRule;
            },
        };
    }

    for (smpds.array.items[3].object.keys(), smpds.array.items[2].object.keys().len..) |name, j| {
        const r = smpds.array.items[3].object.get(name).?.array;

        const sm_l = blk: switch (r.items[1].array.items[0]) {
            .string => |s| {
                break :blk try arena.dupe([]const u8, &.{s});
            },
            .array => |arr| {
                var sm_l_tmp = try arena.alloc([]const u8, arr.items.len);
                for (arr.items, 0..) |r_name, k| {
                    sm_l_tmp[k] = try arena.dupe(u8, r_name.string);
                }
                break :blk sm_l_tmp;
            },
            else => return JsonError.InvalidSMRule,
        };
        const sm_r = blk: switch (r.items[1].array.items[1]) {
            .string => |s| {
                break :blk try arena.dupe([]const u8, &.{s});
            },
            .array => |arr| {
                var sm_r_tmp = try arena.alloc([]const u8, arr.items.len);
                for (arr.items, 0..) |r_name, k| {
                    sm_r_tmp[k] = try arena.dupe(u8, r_name.string);
                }
                break :blk sm_r_tmp;
            },
            else => return JsonError.InvalidSMRule,
        };

        rules[j] = Rule{
            .name = try arena.dupe(u8, name),
            .from = try arena.dupe(u8, r.items[0].string),
            .to = try arena.dupe(u8, r.items[2].string),
            .typ = RuleType.sm,
            .sm_l = sm_l,
            .sm_r = sm_r,
        };
    }

    const res_smpds = SM_PDS{ .states = states, .alphabet = alphabet, .rules = rules };

    const caret_str = val.array.items[1].string;
    const res = try fullBranchCaretFormula.parse(arena, caret_str);
    var caret: *const RawBranchCaret = undefined;
    switch (res.value) {
        .ok => |caret_raw| {
            caret = caret_raw;
        },
        .err => |_| {
            const pos = getErrorPosition(caret_str, res.index);
            const snippet_length = @min(caret_str.len - res.index, 5);
            std.debug.print("Parsing CTL Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, caret_str[res.index..][0..snippet_length] });
            return CaretParseError.StringParseError;
        },
    }

    switch (val.array.items[2]) {
        .array => {},
        else => {
            std.log.err("Initial configuration is not an array\n", .{});
            return error.StringParseError;
        },
    }

    const init = val.array.items[2];
    switch (init.array.items[1]) {
        .string => {},
        else => {
            std.log.err("Initial configuration stack is not a whitespace-separated string\n", .{});
            return error.StringParseError;
        },
    }
    var seq = std.mem.splitSequence(u8, init.array.items[1].string, " ");

    var stack = std.ArrayList([]const u8){};
    var itt: ?[]const u8 = seq.first();
    while (itt) |it| {
        try stack.append(arena, try arena.dupe(u8, it));
        itt = seq.next();
    }

    var phase = try arena.alloc([]const u8, init.array.items[2].array.items.len);
    for (init.array.items[2].array.items, 0..) |rule, k| {
        phase[k] = try arena.dupe(u8, rule.string);
    }

    const res_init = Conf{
        .state = init.array.items[0].string,
        .stack = try stack.toOwnedSlice(arena),
        .phase = phase,
    };

    switch (val.array.items[3]) {
        .array => {},
        else => {
            std.log.err("Atomic proposition set is not an array\n", .{});
            return error.StringParseError;
        },
    }

    const aps = val.array.items[3].array;
    const valuations = try arena.alloc(Valuation, aps.items.len);
    for (aps.items, 0..) |ap_pair, i| {
        switch (ap_pair) {
            .string => |ap_str| {
                const val_res = try ap_definition_grammar_finished.parse(arena, ap_str);
                switch (val_res.value) {
                    .ok => |valuation| {
                        valuations[i] = valuation;
                    },
                    .err => {
                        const pos = getErrorPosition(ap_str, val_res.index);

                        const snippet_length = @min(ap_str.len - val_res.index, 5);
                        std.debug.print("Parsing AP Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, ap_str[val_res.index..][0..snippet_length] });

                        return error.StringParseError;
                    },
                }
            },
            else => {
                std.log.err("Atomic proposition is not a string\n", .{});
                return error.StringParseError;
            },
        }
    }

    return ParsedSMPDS{
        .smpds = res_smpds,
        .branchcaret = BranchCaretLogic{
            .formula = caret,
            .valuations = valuations,
        },
        .init = res_init,
    };
}

pub fn parseString(arena: std.mem.Allocator, str: []const u8) union(enum) {
    ok: ParsedSMPDS,
    err: anyerror,
    invalid_syntax: struct {
        line: usize,
        col: usize,
    },
} {
    const sm_dpds_res: mecha.Result(ParsedSMPDS) = sm_pds_grammar.parse(arena, str) catch |e| return .{ .err = e };
    switch (sm_dpds_res.value) {
        .ok => |val| {
            return .{ .ok = val };
        },
        .err => |_| {
            const pos = getErrorPosition(str, sm_dpds_res.index);
            return .{
                .invalid_syntax = .{ .line = pos.line, .col = pos.col },
            };
        },
    }
}

pub const CaretMode = enum { g, a, c };

pub const RawBranchCaret = union(enum) {
    ap: []const u8,
    top,
    bot,
    not_ap: []const u8,
    lor: struct {
        left: *const RawBranchCaret,
        right: *const RawBranchCaret,
    },
    land: struct {
        left: *const RawBranchCaret,
        right: *const RawBranchCaret,
    },
    A: *const RawBranchCaret,
    E: *const RawBranchCaret,
    R: struct {
        mode: CaretMode,
        left: *const RawBranchCaret,
        right: *const RawBranchCaret,
    },
    U: struct {
        mode: CaretMode,
        left: *const RawBranchCaret,
        right: *const RawBranchCaret,
    },
    X: struct {
        mode: CaretMode,
        next: *const RawBranchCaret,
    },
};

pub fn freeCaret(gpa: std.mem.Allocator, f: *const RawBranchCaret) void {
    switch (f.*) {
        .ap => |n| gpa.free(n),
        .not_ap => |n| gpa.free(n),
        .A => |n| freeCaret(gpa, n),
        .E => |n| freeCaret(gpa, n),
        .X => |n| freeCaret(gpa, n.next),
        .U => |n| {
            freeCaret(gpa, n.left);
            freeCaret(gpa, n.right);
        },
        .R => |n| {
            freeCaret(gpa, n.left);
            freeCaret(gpa, n.right);
        },
        .top, .bot => {},
    }
    gpa.destroy(f);
}

fn fromStr(comptime parser: mecha.Parser([]const u8)) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_str: mecha.Result([]const u8) = try parser.parse(allocator, str);
            return switch (res_str.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawBranchCaret);
                    caret.* = RawBranchCaret{ .ap = res_str.value.ok };
                    break :blk Res.ok(res_str.index, caret);
                },
                .err => Res.err(res_str.index),
            };
        }
    }.parse };
}
fn fromNotStr(comptime parser: mecha.Parser([]const u8)) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_str: mecha.Result([]const u8) = try parser.parse(allocator, str);
            return switch (res_str.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawBranchCaret);
                    caret.* = RawBranchCaret{ .not_ap = res_str.value.ok };
                    break :blk Res.ok(res_str.index, caret);
                },
                .err => Res.err(res_str.index),
            };
        }
    }.parse };
}

fn fromLor(comptime parser: mecha.Parser(std.meta.Tuple(&.{ *const RawBranchCaret, ?std.meta.Tuple(&.{ []const u8, *const RawBranchCaret }) }))) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => |res| blk: {
                    if (res.@"1") |rhs| {
                        const caret = try allocator.create(RawBranchCaret);
                        caret.* = RawBranchCaret{ .lor = .{ .left = res.@"0", .right = rhs.@"1" } };
                        break :blk Res.ok(res_comb.index, caret);
                    } else {
                        break :blk Res.ok(res_comb.index, res.@"0");
                    }
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromLand(comptime parser: mecha.Parser(std.meta.Tuple(&.{ *const RawBranchCaret, ?std.meta.Tuple(&.{ []const u8, *const RawBranchCaret }) }))) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => |res| blk: {
                    if (res.@"1") |rhs| {
                        const caret = try allocator.create(RawBranchCaret);
                        caret.* = RawBranchCaret{ .land = .{ .left = res.@"0", .right = rhs.@"1" } };
                        break :blk Res.ok(res_comb.index, caret);
                    } else {
                        break :blk Res.ok(res_comb.index, res.@"0");
                    }
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromE(comptime parser: mecha.Parser(*const RawBranchCaret)) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(*const RawBranchCaret) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawBranchCaret);
                    caret.* = RawBranchCaret{ .E = res_comb.value.ok.@"0" };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}
fn fromA(comptime parser: mecha.Parser(*const RawBranchCaret)) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(*const RawBranchCaret) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawBranchCaret);
                    caret.* = RawBranchCaret{ .A = res_comb.value.ok.@"0" };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

const caret_top: RawBranchCaret = .top;
const caret_bot: RawBranchCaret = .bot;

const id_grammar = mecha.oneOf(.{
    mecha.combine(.{
        mecha.ascii.range('a', 'z'),
        mecha.oneOf(.{
            mecha.ascii.range('a', 'z'),
            mecha.ascii.range('A', 'Z'),
            mecha.ascii.char('_'),
            mecha.ascii.range('0', '9'),
        }).many(.{}),
    }).asStr(),
    mecha.combine(.{
        mecha.ascii.char('@').discard(),
        mecha.ascii.char('"').discard(),
        chars,
        mecha.ascii.char('"').discard(),
    }),
});
const chars = char.many(.{}).asStr();
const char = mecha.oneOf(.{
    mecha.ascii.not(mecha.oneOf(.{ mecha.ascii.char('"'), mecha.ascii.char('\\') })),
    mecha.combine(.{
        mecha.ascii.char('\\').discard(),
        escape,
    }),
});

const escape = mecha.oneOf(.{
    mecha.ascii.char('"'),
    mecha.ascii.char('\\'),
    mecha.ascii.char('/'),
    mecha.ascii.char('b'),
    mecha.ascii.char('f'),
    mecha.ascii.char('n'),
    mecha.ascii.char('r'),
    mecha.ascii.char('t'),
});

const ap = mecha.oneOf(.{
    mecha.combine(.{ token(mecha.string("!")), fromNotStr(id_grammar) }),
    fromStr(id_grammar),
});

const formulaQuantified = fromQuantified(mecha.combine(.{ mecha.oneOf(.{ mecha.string("A"), mecha.string("E") }), ws, formulaModal }));
const formulaModal = mecha.oneOf(.{
    fromX(mecha.combine(.{ mecha.oneOf(.{ mecha.string("Xg"), mecha.string("Xa"), mecha.string("Xc") }), ws, formula })),
    fromUR(mecha.combine(.{
        formula,
        ws,
        mecha.oneOf(.{
            mecha.string("Ug"),
            mecha.string("Ua"),
            mecha.string("Uc"),
            mecha.string("Rg"),
            mecha.string("Ra"),
            mecha.string("Rc"),
        }),
        ws,
        formula,
    })),

    mecha.combine(.{ token(mecha.string("[")), mecha.ref(formulaModalRef), ws, token(mecha.string("]")) }),
});

const formula = fromLor(mecha.combine(.{
    formula2,
    ws,
    mecha.combine(.{ mecha.string("||"), ws, mecha.ref(formulaRefFn) }).opt(),
}));

const formula2 = fromLand(mecha.combine(.{
    formula3,
    ws,
    mecha.combine(.{ mecha.string("&&"), ws, mecha.ref(formula2RefFn) }).opt(),
}));

const formula3 = mecha.oneOf(.{
    mecha.string("True").mapConst(&caret_top),
    mecha.string("False").mapConst(&caret_bot),
    mecha.ref(formulaQuantifiedRef),
    ap,
    mecha.combine(.{ token(mecha.string("(")), mecha.ref(formulaRefFn), token(mecha.string(")")) }),
    // mecha.combine(.{ token(mecha.string("[")), mecha.ref(formulaRefFn), token(mecha.string("]")) }),
});

fn formulaRefFn() mecha.Parser(*const RawBranchCaret) {
    return formula;
}

fn formula2RefFn() mecha.Parser(*const RawBranchCaret) {
    return formula2;
}

fn formulaQuantifiedRef() mecha.Parser(*const RawBranchCaret) {
    return formulaQuantified;
}

fn formulaModalRef() mecha.Parser(*const RawBranchCaret) {
    return formulaModal;
}

fn fromQuantified(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, *const RawBranchCaret }))) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{
        .parse = (struct {
            fn parse(allocator: std.mem.Allocator, str: []const u8) !mecha.Result(*const RawBranchCaret) {
                const res_comb = try parser.parse(allocator, str);
                return switch (res_comb.value) {
                    .ok => |res| blk: {
                        const caret = try allocator.create(RawBranchCaret);
                        if (std.mem.eql(u8, res.@"0", "A")) {
                            caret.* = .{ .A = res.@"1" };
                        } else {
                            caret.* = .{ .E = res.@"1" };
                        }
                        break :blk Res.ok(res_comb.index, caret);
                    },
                    .err => Res.err(res_comb.index),
                };
            }
        }.parse),
    };
}
fn fromX(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, *const RawBranchCaret }))) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{
        .parse = (struct {
            pub fn parse(allocator: std.mem.Allocator, str: []const u8) !mecha.Result(*const RawBranchCaret) {
                const res_comb = try parser.parse(allocator, str);
                return switch (res_comb.value) {
                    .ok => |res| blk: {
                        const caret = try allocator.create(RawBranchCaret);
                        const mode: CaretMode =
                            if (std.mem.eql(u8, res.@"0", "Xg")) .g else if (std.mem.eql(u8, res.@"0", "Xa")) .a else .c;
                        caret.* = .{ .X = .{ .mode = mode, .next = res.@"1" } };
                        break :blk Res.ok(res_comb.index, caret);
                    },
                    .err => Res.err(res_comb.index),
                };
            }
        }.parse),
    };
}

fn fromUR(comptime parser: mecha.Parser(std.meta.Tuple(&.{ *const RawBranchCaret, []const u8, *const RawBranchCaret }))) mecha.Parser(*const RawBranchCaret) {
    const Res = mecha.Result(*const RawBranchCaret);
    return .{ .parse = (struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ *const RawBranchCaret, []const u8, *const RawBranchCaret })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => |res| blk: {
                    const caret = try allocator.create(RawBranchCaret);
                    if (std.mem.eql(u8, res.@"1", "Ug")) {
                        caret.* = RawBranchCaret{ .U = .{
                            .mode = .g,
                            .left = res.@"0",
                            .right = res.@"2",
                        } };
                        break :blk Res.ok(res_comb.index, caret);
                    }
                    if (std.mem.eql(u8, res.@"1", "Ua")) {
                        caret.* = RawBranchCaret{ .U = .{
                            .mode = .a,
                            .left = res.@"0",
                            .right = res.@"2",
                        } };
                        break :blk Res.ok(res_comb.index, caret);
                    }
                    if (std.mem.eql(u8, res.@"1", "Uc")) {
                        caret.* = RawBranchCaret{ .U = .{
                            .mode = .c,
                            .left = res.@"0",
                            .right = res.@"2",
                        } };
                        break :blk Res.ok(res_comb.index, caret);
                    }
                    if (std.mem.eql(u8, res.@"1", "Rg")) {
                        caret.* = RawBranchCaret{ .R = .{
                            .mode = .g,
                            .left = res.@"0",
                            .right = res.@"2",
                        } };
                        break :blk Res.ok(res_comb.index, caret);
                    }
                    if (std.mem.eql(u8, res.@"1", "Ra")) {
                        caret.* = RawBranchCaret{ .R = .{
                            .mode = .a,
                            .left = res.@"0",
                            .right = res.@"2",
                        } };
                        break :blk Res.ok(res_comb.index, caret);
                    }
                    if (std.mem.eql(u8, res.@"1", "Rc")) {
                        caret.* = RawBranchCaret{ .R = .{
                            .mode = .c,
                            .left = res.@"0",
                            .right = res.@"2",
                        } };
                        break :blk Res.ok(res_comb.index, caret);
                    }
                    unreachable;
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse) };
}

const fullBranchCaretFormula = mecha.combine(.{ formula, mecha.eos });

fn token(comptime parser: anytype) mecha.Parser(void) {
    return mecha.combine(.{ parser.discard(), ws });
}

const comment = mecha.combine(.{ mecha.string("//").discard(), mecha.utf8.not(mecha.utf8.char(0x000A)).many(.{}).discard(), mecha.utf8.char(0x000A) });
const ml_comment: mecha.Parser(u21) = mecha.combine(.{
    mecha.string("/*").discard(),
    mecha.oneOf(.{
        mecha.ascii.not(mecha.ascii.char('*')).asStr(),
        mecha.combine(.{ mecha.ascii.char('*').many(.{ .min = 1 }), mecha.ascii.not(mecha.ascii.char('/')) }).asStr(),
    }).many(.{}).discard(),
    mecha.ascii.char('*').many(.{ .min = 1 }).discard(),
    mecha.utf8.char('/'),
});

const ws = mecha.oneOf(.{
    comment,
    ml_comment,
    mecha.utf8.char(0x0020),
    mecha.utf8.char(0x000A),
    mecha.utf8.char(0x000D),
    mecha.utf8.char(0x0009),
}).many(.{ .collect = false }).discard();

fn PopRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.internal,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn StandardRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.internal,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                    .new_top = res_comb.value.ok.@"4",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn PushRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.internal,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                    .new_top = res_comb.value.ok.@"4",
                    .new_tail = res_comb.value.ok.@"5",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn SMRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, [][]const u8, [][]const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, [][]const u8, [][]const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    std.mem.sort([]const u8, res_comb.value.ok.@"2", {}, lt);
                    std.mem.sort([]const u8, res_comb.value.ok.@"3", {}, lt);
                    break :blk Res.ok(res_comb.index, Rule{
                        .typ = RuleType.sm,
                        .name = res_comb.value.ok.@"0",
                        .from = res_comb.value.ok.@"1",
                        .sm_l = res_comb.value.ok.@"2",
                        .sm_r = res_comb.value.ok.@"3",
                        .to = res_comb.value.ok.@"4",
                    });
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn CallRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.call,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                    .new_top = res_comb.value.ok.@"4",
                    .new_tail = res_comb.value.ok.@"5",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn RetRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.ret,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn SMPDSParser(comptime parser: mecha.Parser([]Rule)) mecha.Parser(SM_PDS) {
    const Res = mecha.Result(SM_PDS);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            var states = std.StringArrayHashMap(void).init(allocator);
            var alphabet = std.StringArrayHashMap(void).init(allocator);
            var rules = std.ArrayList(Rule){};

            const res_comb: mecha.Result([]Rule) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => |val| blk: {
                    for (val) |rule| {
                        try rules.append(allocator, rule);
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
                    const states_sorted = try allocator.dupe([]const u8, states.keys());
                    std.mem.sort([]const u8, states_sorted, {}, lt);
                    const alphabet_sorted = try allocator.dupe([]const u8, alphabet.keys());
                    std.mem.sort([]const u8, alphabet_sorted, {}, lt);
                    const smdpds = SM_PDS{
                        .states = states_sorted,
                        .alphabet = alphabet_sorted,
                        .rules = rules.items,
                    };
                    break :blk Res.ok(res_comb.index, smdpds);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

const id_sequence = id_grammar.many(.{ .separator = ws });

const sm_pds_rule_grammar = mecha.oneOf(.{
    RetRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("+>")), id_grammar, ws, token(mecha.string(";")) })),
    CallRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("+>")), id_grammar, ws, id_grammar, ws, id_grammar, ws, token(mecha.string(";")) })),

    PopRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("->")), id_grammar, ws, token(mecha.string(";")) })),
    StandardRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("->")), id_grammar, ws, id_grammar, ws, token(mecha.string(";")) })),
    PushRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("->")), id_grammar, ws, id_grammar, ws, id_grammar, ws, token(mecha.string(";")) })),
    SMRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, token(mecha.string("-(")), id_sequence, ws, token(mecha.string("/")), id_sequence, ws, token(mecha.string(")->")), id_grammar, ws, token(mecha.string(";")) })),
});

pub const Regex = union(enum) {
    u: struct {
        left: *const Regex,
        right: *const Regex,
    },
    c: struct {
        left: *const Regex,
        right: *const Regex,
    },
    star: *const Regex,
    symbol: []const u8,
    anysymbol: void,
    epsilon: void,

    pub fn format(
        self: @This(),
        writer: *std.io.Writer,
    ) !void {
        return switch (self) {
            .symbol => |sym| try writer.print("{s}", .{sym}),
            .anysymbol => try writer.print(".", .{}),
            .epsilon => try writer.print("\\e", .{}),
            .star => |t| try writer.print("({f})*", .{t}),
            .u => |t| try writer.print("({f}) | ({f})", .{ t.left, t.right }),
            .c => |t| try writer.print("({f}) + ({f})", .{ t.left, t.right }),
        };
    }
};

fn fromUnion(comptime parser: mecha.Parser(std.meta.Tuple(&.{ *const Regex, *const Regex }))) mecha.Parser(*const Regex) {
    const Res = mecha.Result(*const Regex);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ *const Regex, *const Regex })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const reg = try allocator.create(Regex);
                    reg.* = Regex{ .u = .{ .left = res_comb.value.ok.@"0", .right = res_comb.value.ok.@"1" } };
                    break :blk Res.ok(res_comb.index, reg);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromConcat(comptime parser: mecha.Parser(std.meta.Tuple(&.{ *const Regex, *const Regex }))) mecha.Parser(*const Regex) {
    const Res = mecha.Result(*const Regex);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ *const Regex, *const Regex })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const reg = try allocator.create(Regex);
                    reg.* = Regex{ .c = .{ .left = res_comb.value.ok.@"0", .right = res_comb.value.ok.@"1" } };
                    break :blk Res.ok(res_comb.index, reg);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromStar(comptime parser: mecha.Parser(*const Regex)) mecha.Parser(*const Regex) {
    const Res = mecha.Result(*const Regex);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(*const Regex) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const reg = try allocator.create(Regex);
                    reg.* = Regex{ .star = res_comb.value.ok };
                    break :blk Res.ok(res_comb.index, reg);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromToken(comptime parser: mecha.Parser([]const u8)) mecha.Parser(*const Regex) {
    const Res = mecha.Result(*const Regex);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result([]const u8) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const reg = try allocator.create(Regex);
                    reg.* = Regex{ .symbol = res_comb.value.ok };
                    break :blk Res.ok(res_comb.index, reg);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

const regex_grammar = regex_grammar_u;
const regex_grammar_u = mecha.oneOf(.{
    fromUnion(mecha.combine(.{ regex_grammar_c, ws, token(mecha.string("|")), mecha.ref(regex_u) })),
    regex_grammar_c,
});

fn regex_u() mecha.Parser(*const Regex) {
    return regex_grammar_u;
}

const regex_grammar_c = mecha.oneOf(.{
    fromConcat(mecha.combine(.{ regex_grammar_s, ws, token(mecha.string("+")), mecha.ref(regex_c) })),
    regex_grammar_s,
});

fn regex_c() mecha.Parser(*const Regex) {
    return regex_grammar_c;
}

const regex_grammar_s = mecha.oneOf(.{
    fromStar(mecha.combine(.{ regex_grammar_t, ws, token(mecha.string("*")) })),
    regex_grammar_t,
});

fn regex_s() mecha.Parser(*const Regex) {
    return regex_grammar_s;
}

pub const anysym = Regex{ .anysymbol = {} };
pub const epsilon = Regex{ .epsilon = {} };

const regex_grammar_t = mecha.oneOf(.{
    token(mecha.string(".")).mapConst(&anysym),
    mecha.combine(.{ token(mecha.string("(")), mecha.ref(regex_u), ws, token(mecha.string(")")) }),
    fromToken(id_grammar),
});

pub const SimpleValuation = struct {
    state: ?[]const u8,
    top: []const u8,
};

pub const RegularValuation = struct {
    state: ?[]const u8,
    regex: *const Regex,
};

pub const APValuation = union(enum) {
    state: []const u8,
    simple: SimpleValuation,
    regular: RegularValuation,
};

pub const Valuation = struct {
    ap: []const u8,
    val: APValuation,
};

pub const BranchCaretLogic = struct {
    formula: *const RawBranchCaret,
    valuations: []const Valuation,
};

pub const RegOrSimple = union(enum) {
    reg: *const Regex,
    simple: []const u8,
};

const ap_valuation =
    mecha.combine(.{
        mecha.oneOf(.{ id_grammar, mecha.string("*") }),
        ws,
        mecha.combine(.{
            token(mecha.string(":")),
            mecha.oneOf(.{
                mecha.combine(.{
                    token(mecha.string("/")),
                    regex_grammar,
                    token(mecha.string("/")),
                }).map(struct {
                    fn map(res: *const Regex) RegOrSimple {
                        return RegOrSimple{ .reg = res };
                    }
                }.map),
                mecha.combine(.{
                    id_grammar,
                    ws,
                    token(mecha.string(".")),
                    token(mecha.string("*")),
                }).map(struct {
                    fn map(res: []const u8) RegOrSimple {
                        return RegOrSimple{ .simple = res };
                    }
                }.map),
            }),
        }).opt(),
    }).map(struct {
        fn map(res: std.meta.Tuple(&.{ []const u8, ?RegOrSimple })) APValuation {
            const st = if (std.mem.eql(u8, res.@"0", "*")) null else res.@"0";
            if (res.@"1") |rs| {
                switch (rs) {
                    .reg => |r| {
                        return APValuation{ .regular = RegularValuation{
                            .regex = r,
                            .state = st,
                        } };
                    },
                    .simple => |s| {
                        return APValuation{ .simple = SimpleValuation{
                            .top = s,
                            .state = st,
                        } };
                    },
                }
            } else {
                return APValuation{ .state = res.@"0" };
            }
        }
    }.map);

const ap_definition_grammar = mecha.combine(.{
    id_grammar, ws, token(mecha.string(":=")), ap_valuation,
}).map(struct {
    fn map(res: std.meta.Tuple(&.{ []const u8, APValuation })) Valuation {
        return Valuation{
            .ap = res.@"0",
            .val = res.@"1",
        };
    }
}.map);

const ap_definition_grammar_finished = mecha.combine(.{ ap_definition_grammar, mecha.eos });

const branchcaret_grammar = mecha.oneOf(.{
    mecha.combine(.{
        token(mecha.string("branchcaret")),
        token(mecha.string("{")),
        formula,
        ws,
        token(mecha.string("where")),
        token(mecha.string("[")),
        ap_definition_grammar.many(.{ .separator = mecha.combine(.{ ws, token(mecha.string(",")) }) }),
        ws,
        token(mecha.string("]")),
        token(mecha.string("}")),
    }).map(struct {
        fn map(res: std.meta.Tuple(&.{ *const RawBranchCaret, []const Valuation })) BranchCaretLogic {
            return BranchCaretLogic{
                .formula = res.@"0",
                .valuations = res.@"1",
            };
        }
    }.map),

    mecha.combine(.{ token(mecha.string("branchcaret")), token(mecha.string("{")), formula, ws, token(mecha.string("}")) }).map(struct {
        fn map(res: *const RawBranchCaret) BranchCaretLogic {
            return BranchCaretLogic{
                .formula = res,
                .valuations = &.{},
            };
        }
    }.map),
});

const sm_pds_grammar = mecha.combine(.{
    ws,
    init_state_grammar,
    branchcaret_grammar,
    SMPDSParser(sm_pds_rule_grammar.many(.{ .separator = ws })),
    ws,
    mecha.eos,
}).map(struct {
    fn map(res: std.meta.Tuple(&.{ Conf, BranchCaretLogic, SM_PDS })) ParsedSMPDS {
        return ParsedSMPDS{
            .init = res.@"0",
            .branchcaret = res.@"1",
            .smpds = res.@"2",
        };
    }
}.map);

const init_state_grammar = mecha.combine(.{
    token(mecha.string("init")),
    id_grammar,
    ws,
    id_sequence,
    ws,
    token(mecha.string("#")),
    id_sequence,
    ws,
    token(mecha.string(";")),
})
    .map(struct {
    fn map(res: std.meta.Tuple(&.{ []const u8, [][]const u8, [][]const u8 })) Conf {
        return Conf{
            .state = res.@"0",
            .stack = res.@"1",
            .phase = res.@"2",
        };
    }
}.map);

pub const ParsedSMPDS = struct {
    init: Conf,
    branchcaret: BranchCaretLogic,
    smpds: SM_PDS,
};

pub fn lt(_: void, lhs: []const u8, rhs: []const u8) bool {
    return std.mem.order(u8, lhs, rhs) == .lt;
}

pub const ErrorPos = struct {
    line: usize,
    col: usize,
};

fn getErrorPosition(str: []const u8, pos: usize) ErrorPos {
    var start_pos: usize = 0;
    var line_counter: usize = 1;
    while (true) {
        const nl_pos = std.mem.indexOfPos(u8, str, start_pos, "\n") orelse str.len;
        if (pos <= nl_pos) {
            return ErrorPos{
                .line = line_counter,
                .col = pos - start_pos + 1,
            };
        }
        start_pos = nl_pos + 1;
        line_counter += 1;
        if (nl_pos == str.len) {
            break;
        }
    }
    return ErrorPos{ .line = line_counter, .col = 1 };
}

pub const SmpdsFile = struct {
    arena: std.heap.ArenaAllocator,
    filename: []const u8,

    pub fn open(allocator: std.mem.Allocator, filename: []const u8) SmpdsFile {
        return SmpdsFile{
            .arena = std.heap.ArenaAllocator.init(allocator),
            .filename = filename,
        };
    }

    pub fn close(self: *@This()) void {
        self.arena.deinit();
    }

    /// This struct still owns the memory of the result, if you need to close the file, then first deep copy the result to other place
    pub fn parse(self: *@This()) !ParsedSMPDS {
        var file = try std.fs.cwd().openFile(self.filename, .{});
        defer file.close();

        var file_contents = std.ArrayList(u8){};
        try file_contents.ensureTotalCapacity(self.arena.allocator(), (try file.stat()).size);

        var buf: [1024]u8 = undefined;
        while (true) {
            const bytenum = try file.read(&buf);
            if (bytenum == 0) break;
            try file_contents.appendSlice(self.arena.allocator(), buf[0..bytenum]);
        }
        // std.debug.print("{s}\n---\n", .{file_contents.items});
        const sm_dpds_res: mecha.Result(ParsedSMPDS) = try sm_pds_grammar.parse(self.arena.allocator(), file_contents.items);
        switch (sm_dpds_res.value) {
            .ok => |val| {
                return val;
            },
            .err => |_| {
                const pos = getErrorPosition(file_contents.items, sm_dpds_res.index);
                const snippet_length = @min(file_contents.items.len - sm_dpds_res.index, 5);
                std.debug.print("Parsing SM-PDS Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, file_contents.items[sm_dpds_res.index..][0..snippet_length] });
                return CaretParseError.StringParseError;
            },
        }
    }
};

pub const CaretParseError = error{
    APNotInStates,
    StringParseError,
};

test "branchcaret formula" {
    const strs: [2][]const u8 = .{ "A[ False Rg p1 ]", "E Xa p1" };
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    for (strs) |str| {
        const res = try fullBranchCaretFormula.parse(allocator, str);
        switch (res.value) {
            .ok => |_| {},
            .err => {
                const pos = getErrorPosition(str, res.index);

                const snippet_length = @min(str.len - res.index, 5);
                std.debug.print("Parsing Caret '{s}' Error at line {d}, column {d}:\n{s}...\n", .{ str, pos.line, pos.col, str[res.index..][0..snippet_length] });
                try std.testing.expect(false);
            },
        }
    }
}

test "simple val" {
    const str = "p4: gamma1 .*";
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const res = try ap_valuation.parse(allocator, str);
    switch (res.value) {
        .ok => |val| {
            const cor = APValuation{
                .simple = SimpleValuation{
                    .state = "p4",
                    .top = "gamma1",
                },
            };
            try std.testing.expectEqualDeep(cor, val);
        },
        .err => {
            const pos = getErrorPosition(str, res.index);

            const snippet_length = @min(str.len - res.index, 5);
            std.debug.print("Parsing Caret Logic Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, str[res.index..][0..snippet_length] });
            try std.testing.expect(false);
        },
    }
}

test "branchcaret formula with valuations" {
    const str = "branchcaret{ E[ True Rc p2 && E Xa p1 ] where [ p1 := p2, p3 := p4: gamma1 .* ]}";
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const res = try branchcaret_grammar.parse(allocator, str);
    switch (res.value) {
        .ok => |caret_logic| {
            const correct_val: []const Valuation = &.{
                Valuation{
                    .ap = "p1",
                    .val = APValuation{
                        .state = "p2",
                    },
                },
                Valuation{
                    .ap = "p3",
                    .val = APValuation{
                        .simple = SimpleValuation{
                            .state = "p4",
                            .top = "gamma1",
                        },
                    },
                },
            };
            try std.testing.expectEqualDeep(correct_val, caret_logic.valuations);
        },
        .err => {
            const pos = getErrorPosition(str, res.index);

            const snippet_length = @min(str.len - res.index, 5);
            std.debug.print("Parsing Caret Logic Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, str[res.index..][0..snippet_length] });
            try std.testing.expect(false);
        },
    }
}

test "smpds file" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var file = SmpdsFile.open(allocator, "examples/example.smpds");
    _ = try file.parse();
}

test "caret formula with regular valuations" {
    const str = "branchcaret{ A [False Rg p1] where [ p1 := p2 : /gamma1 + gamma2 * + (gamma1 | gamma2)* + .*/, p3 := p4: /gamma1 + .* /]}";
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const res = try branchcaret_grammar.parse(allocator, str);
    switch (res.value) {
        .ok => |caret_logic| {
            const correct_val: []const Valuation = &.{
                Valuation{
                    .ap = "p1",
                    .val = APValuation{
                        .regular = RegularValuation{
                            .state = "p2",
                            .regex = &Regex{
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
                            },
                        },
                    },
                },
                Valuation{
                    .ap = "p3",
                    .val = APValuation{ .regular = RegularValuation{
                        .state = "p4",
                        .regex = &Regex{
                            .c = .{
                                .left = &Regex{
                                    .symbol = "gamma1",
                                },
                                .right = &Regex{
                                    .star = &Regex{
                                        .anysymbol = {},
                                    },
                                },
                            },
                        },
                    } },
                },
            };
            try std.testing.expectEqualDeep(correct_val, caret_logic.valuations);
        },
        .err => {
            const pos = getErrorPosition(str, res.index);

            const snippet_length = @min(str.len - res.index, 5);
            std.debug.print("Parsing Caret Logic Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, str[res.index..][0..snippet_length] });
            try std.testing.expect(false);
        },
    }
}

test "rule parser" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var res: mecha.Result(Rule) = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 -> p2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.internal);
            try std.testing.expectEqual(val.new_top, null);
            try std.testing.expectEqual(val.new_tail, null);
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 -> p2 g2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.internal);
            try std.testing.expectEqualStrings(val.new_top.?, "g2");
            try std.testing.expectEqual(val.new_tail, null);
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 -> p2 g2 g3;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.internal);
            try std.testing.expectEqualStrings(val.new_top.?, "g2");
            try std.testing.expectEqualStrings(val.new_tail.?, "g3");
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 -( r1 r2 r3 / r4 r5 )-> p2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqual(val.top, null);
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.sm);
            try std.testing.expectEqual(val.new_top, null);
            try std.testing.expectEqual(val.new_tail, null);
            const correct_l: []const []const u8 = &.{ "r1", "r2", "r3" };
            const correct_r: []const []const u8 = &.{ "r4", "r5" };
            try std.testing.expectEqualDeep(val.sm_l.?, correct_l);
            try std.testing.expectEqualDeep(val.sm_r.?, correct_r);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 +> p2 g2 g1;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.call);
            try std.testing.expectEqualStrings(val.new_top.?, "g2");
            try std.testing.expectEqualStrings(val.new_tail.?, "g1");
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            std.debug.print("Error at {any}\n", .{res.index});
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 +> p2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.ret);
            try std.testing.expectEqual(val.new_top, null);
            try std.testing.expectEqual(val.new_tail, null);
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            std.debug.print("Error at {any}\n", .{res.index});
            try std.testing.expect(false);
        },
    }

    const example =
        \\// this is example
        \\ init p3 g1 # r1 r2 r4;
        \\
        \\ branchcaret {p1 || A Xg p2}
        \\ r1: p1 g1 ->
        \\      // the parser should read comments anywhere
        \\      p2 g2;
        \\ r2: p1 g1 -> p2 g2 g3;
        \\ // inclduing here
        \\
        \\ r11: p3 g1 -> p5 g2; // and here
        \\
        \\ r12: p4 g1 +> p6 g2 g3;
        \\ r13: p5 g1 -> p3 g2;
        \\ r14: p6 g1 -> p6 g2 g3;
        \\ /**********
        \\ * we should be able to
        \\ * write multi**-line comment
        \\ * like this**
        \\ ***************/
    ;

    const sm_pds_res: mecha.Result(ParsedSMPDS) = try sm_pds_grammar.parse(allocator, example);
    switch (sm_pds_res.value) {
        .ok => |val_conf| {
            const init: Conf = .{
                .state = "p3",
                .stack = &.{"g1"},
                .phase = &.{ "r1", "r2", "r4" },
            };
            try std.testing.expectEqualDeep(init, val_conf.init);
            const val = val_conf;
            const states1: []const []const u8 = &.{ "p1", "p2", "p3", "p4", "p5", "p6" };
            const alphabet1: []const []const u8 = &.{ "g1", "g2", "g3" };
            try std.testing.expectEqualDeep(states1, val.smpds.states);
            try std.testing.expectEqualDeep(alphabet1, val.smpds.alphabet);
            try std.testing.expectEqual(6, val.smpds.rules.len);
            try std.testing.expectEqualDeep(&RawBranchCaret{ .lor = .{
                .left = &RawBranchCaret{ .ap = "p1" },
                .right = &RawBranchCaret{
                    .A = &RawBranchCaret{
                        .X = .{ .mode = .g, .next = &RawBranchCaret{ .ap = "p2" } },
                    },
                },
            } }, val.branchcaret.formula);
        },
        .err => |_| {
            std.debug.print("Error at {any}\n", .{getErrorPosition(example, sm_pds_res.index)});
            try std.testing.expect(false);
        },
    }
}

test "unprocessed printing" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    {
        const r1 = Rule{
            .name = "r1",
            .typ = RuleType.internal,
            .from = "p1",
            .to = "p2",
            .top = "g1",
            .new_top = "g2",
        };
        _ = &r1;
        const str = try std.fmt.allocPrint(allocator, "{f}", .{r1});
        const test_str = "r1: p1 g1 \\--> p2 g2 -";
        try std.testing.expectEqualStrings(str, test_str);
    }

    {
        const r1 = Rule{
            .name = "r1",
            .typ = RuleType.call,
            .from = "p1",
            .to = "p2",
            .top = "g1",
            .new_top = "g2",
            .new_tail = "g3",
        };
        _ = &r1;
        const str = try std.fmt.allocPrint(allocator, "{f}", .{r1});
        const test_str = "r1: p1 g1 \\-call-> p2 g2 g3";
        try std.testing.expectEqualStrings(str, test_str);
    }

    {
        const r1 = Rule{
            .name = "r1",
            .typ = RuleType.sm,
            .from = "p1",
            .to = "p2",
            .sm_l = &[_][]const u8{"r1"},
            .sm_r = &[_][]const u8{ "r1", "r2", "r3" },
        };
        _ = &r1;
        const str = try std.fmt.allocPrint(allocator, "{f}", .{r1});
        const test_str = "r1: p1 \\--(r1)-/-(r1, r2, r3)--> p2";
        try std.testing.expectEqualStrings(str, test_str);
    }
}

test "python parse" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const parsed = try parseJsonFromPython(std.testing.allocator, allocator, "examples/python_example.json");
    // defer freeCaret(std.testing.allocator, parsed.caret.formula);
    _ = parsed;
}
