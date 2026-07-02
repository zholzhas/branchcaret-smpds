import hashlib
import json
import os
import random
import re
import subprocess

OFFSET = 0


def generateRandomPDS(
    number_of_states, alphabet_size, number_of_rules, number_of_smrules
):
    global OFFSET
    OFFSET = 0

    assert (
        number_of_rules
        < number_of_states
        * alphabet_size
        * number_of_states
        * alphabet_size
        * alphabet_size
    )

    states = []
    loop_states = []
    for j in range(number_of_states):
        name = "p{}".format(OFFSET)
        states.append(name)
        if random.randint(0, 3) == 1:
            loop_states.append(name)
        OFFSET += 1
    alphabet = []
    for j in range(alphabet_size):
        alphabet.append("y{}".format(OFFSET))
        OFFSET += 1

    rules = {}
    smrules = {}

    for s in loop_states:
        for t in alphabet:
            rule_name = "r{}".format(OFFSET)
            OFFSET += 1
            rules[rule_name] = (s, t, s, t, "int")
            number_of_rules -= 1

    for j in range(number_of_rules):
        from_state = states[random.randint(0, len(states) - 1)]
        to_state = states[random.randint(0, len(states) - 1)]
        gamma_1 = alphabet[random.randint(0, len(alphabet) - 1)]
        w_length = random.randint(0, 2)
        w = ""
        typ = "ret"
        if w_length == 1:
            w = alphabet[random.randint(0, len(alphabet) - 1)]
            typ = "int"
        elif w_length == 2:
            w = "{} {}".format(
                alphabet[random.randint(0, len(alphabet) - 1)],
                alphabet[random.randint(0, len(alphabet) - 1)],
            )
            typ = "call"
        rule_name = "r{}".format(OFFSET)
        OFFSET += 1
        rules[rule_name] = (from_state, gamma_1, to_state, w, typ)

    for j in range(number_of_smrules):
        from_state = states[random.randint(0, len(states) - 1)]
        to_state = states[random.randint(0, len(states) - 1)]

        rule_name = "r{}".format(OFFSET)
        OFFSET += 1
        smrules[rule_name] = (from_state, ("", ""), to_state)

    rule_names = set(rules.keys()).union(smrules.keys())
    for name, smrule in smrules.items():
        av_rules = list(rule_names.difference([name]))
        smrules[name] = (
            smrules[name][0],
            (
                av_rules[random.randint(0, len(av_rules) - 1)],
                av_rules[random.randint(0, len(av_rules) - 1)],
            ),
            smrules[name][2],
        )
    return (states, alphabet, rules, smrules)


def getRandomInit(smpds):
    (states, alphabet, rules, smrules) = smpds
    state = states[random.randint(0, len(states) - 1)]
    word = alphabet[random.randint(0, len(alphabet) - 1)]
    phase = set()
    rule_set = set(rules.keys()).union(smrules.keys())
    for i in range(random.randint(len(rules), len(rules) + len(smrules))):
        phase.add(rule_set.pop())
    return (state, word, frozenset(phase))


def generatePDS(number_of_states, alphabet_size, number_of_rules, number_of_smrules):
    global OFFSET
    OFFSET = 0

    assert (
        number_of_rules
        < number_of_states
        * alphabet_size
        * number_of_states
        * alphabet_size
        * alphabet_size
    )

    states = []
    loop_states = []
    for j in range(number_of_states):
        name = "p{}".format(OFFSET)
        states.append(name)
        if random.randint(0, 20) == 1:
            loop_states.append(name)
        OFFSET += 1
    alphabet = []
    for j in range(alphabet_size):
        alphabet.append("y{}".format(OFFSET))
        OFFSET += 1

    rules = {}
    smrules = {}
    init_state = states[random.randint(0, len(states) - 1)]
    init_word = alphabet[random.randint(0, len(alphabet) - 1)]

    cur_states = list()
    cur_states.append((init_state, init_word))
    returns = list()

    while len(rules) < number_of_rules:
        src, top = cur_states[random.randint(0, len(cur_states) - 1)]
        if top == None:
            top = returns[random.randint(0, len(returns) - 1)]
        num_branches = random.randint(1, 2)
        for i in range(num_branches):
            to_state = states[random.randint(0, len(states) - 1)]

            if len(returns) > 0 and len(smrules) < number_of_smrules:
                rule_typ = random.randint(0, 3)
            elif len(returns) > 0:
                rule_typ = random.randint(0, 2)
            else:
                rule_typ = random.randint(0, 1)
            if rule_typ == 0:
                new_top = alphabet[random.randint(0, len(alphabet) - 1)]
                if (to_state, new_top) not in cur_states:
                    cur_states.append((to_state, new_top))
                rule_name = "r{}".format(OFFSET)
                OFFSET += 1
                rules[rule_name] = (src, top, to_state, new_top, "int")
            if rule_typ == 1:
                new_top = alphabet[random.randint(0, len(alphabet) - 1)]
                ret = alphabet[random.randint(0, len(alphabet) - 1)]
                if (to_state, new_top) not in cur_states:
                    cur_states.append((to_state, new_top))
                if ret not in returns:
                    returns.append(ret)
                rule_name = "r{}".format(OFFSET)
                OFFSET += 1
                rules[rule_name] = (
                    src,
                    top,
                    to_state,
                    "{} {}".format(new_top, ret),
                    "call",
                )

            if rule_typ == 2:
                if (to_state, None) not in cur_states:
                    cur_states.append((to_state, None))
                rule_name = "r{}".format(OFFSET)
                OFFSET += 1
                rules[rule_name] = (src, top, to_state, "", "ret")
            if rule_typ == 3:
                if (to_state, top) not in cur_states:
                    cur_states.append((to_state, top))
                rule_name = "r{}".format(OFFSET)
                OFFSET += 1
                smrules[rule_name] = (
                    src,
                    ("", ""),
                    to_state,
                )

    rule_names = sorted(list(set(rules.keys()).union(smrules.keys())))
    for name, smrule in smrules.items():
        av_rules = rule_names
        smrules[name] = (
            smrules[name][0],
            (
                av_rules[random.randint(0, len(av_rules) - 1)],
                av_rules[random.randint(0, len(av_rules) - 1)],
            ),
            smrules[name][2],
        )

    phase = list()
    rule_set = sorted(list(set(rules.keys()).union(smrules.keys())))
    for i in range(random.randint(len(rules), len(rules) + len(smrules))):
        phase.append(rule_set.pop(random.randint(0, len(rule_set) - 1)))
    return (states, alphabet, rules, smrules), (init_state, init_word, phase)


def getGlobalCaretAux(states, length, level=0):

    if length <= 1:
        if random.randint(0, 1) == 1:
            tmp = states
            cur_state = tmp[random.randint(0, len(tmp) - 1)]
        else:
            cur_state = "!" + states[random.randint(0, len(states) - 1)]
        return cur_state, 1, 0

    cur_state = states[random.randint(0, len(states) - 1)]
    choice = random.randint(1, 4)
    if choice == 1:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "E[True Ug ({} && {})]".format(cur_state, c1), l1 + 2, t1 + 1
    if choice == 2:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "E[(False) Rg (!{} || {})]".format(cur_state, c1), l1 + 2, t1 + 1
    if choice == 3:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "A[(True) Ug ({} && {})]".format(cur_state, c1), l1 + 2, t1 + 1
    if choice == 4:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "A[(False) Rg (!{} || {})]".format(cur_state, c1), l1 + 2, t1 + 1


def getGlobalWithCallerCaretAux(states, length, level=0):
    if length <= 1:
        if random.randint(0, 1) == 1:
            tmp = states
            return tmp[random.randint(0, len(tmp) - 1)], 1, 0
        else:
            return "!" + states[random.randint(0, len(states) - 1)], 1, 0

    choice = random.randint(1, 4)
    if choice == 1:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "E[True Ug ({})]".format(c1), l1 + 1, t1 + 1
    if choice == 2:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "E[(False) Rg ({})]".format(c1), l1 + 1, t1 + 1
    if choice == 3:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "A[(True) Ug ({})]".format(c1), l1 + 1, t1 + 1
    if choice == 4:
        c1, l1, t1 = getGlobalCaretAux(states, length - 1, level)
        return "A[(False) Rg ({})]".format(c1), l1 + 1, t1 + 1


def getAlternateCaretAux(states, length, typ="g", with_c=False):
    if length <= 1:
        if random.randint(0, 1) == 1:
            tmp = states
            cur_state = tmp[random.randint(0, len(tmp) - 1)]
        else:
            cur_state = "!" + states[random.randint(0, len(states) - 1)]
        return cur_state, 1, 0

    cur_state = states[random.randint(0, len(states) - 1)]
    choice = random.randint(1, 4)
    if typ == "g":
        cur_state = states[random.randint(0, len(states) - 1)]
        if with_c:
            if random.randint(0, 1) == 0:
                cur_state = "E[True Uc {}]".format(cur_state)
            else:
                cur_state = "E[False Rc {}]".format(cur_state)

        choice = random.randint(1, 4)
        if choice == 1:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "a", with_c)
            return "E[True Ug ({} && {})]".format(cur_state, c1), l1 + 2, t1 + 1
        if choice == 2:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "a", with_c)
            return "E[(False) Rg (!{} || {})]".format(cur_state, c1), l1 + 2, t1 + 1
        if choice == 3:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "a", with_c)
            return "A[(True) Ug ({} && {})]".format(cur_state, c1), l1 + 2, t1 + 1
        if choice == 4:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "a", with_c)
            return "A[(False) Rg (!{} || {})]".format(cur_state, c1), l1 + 2, t1 + 1
    else:
        if choice == 1:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "g", with_c)
            return "E[True Ua ({} && {})]".format(cur_state, c1), l1 + 2, t1 + 1
        if choice == 2:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "g", with_c)
            return "E[(False) Ra (!{} || {})]".format(cur_state, c1), l1 + 2, t1 + 1
        if choice == 3:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "g", with_c)
            return "A[(True) Ua ({} && {})]".format(cur_state, c1), l1 + 2, t1 + 1
        if choice == 4:
            c1, l1, t1 = getAlternateCaretAux(states, length - 1, "g", with_c)
            return "A[(False) Ra (!{} || {})]".format(cur_state, c1), l1 + 2, t1 + 1


def getRandomCaretAux(states, length, level=0):
    if length < 1:
        if random.randint(0, 1) == 1:
            return states[random.randint(0, len(states) - 1)]
        else:
            return "!" + states[random.randint(0, len(states) - 1)]

    caret_u = ["Ua", "Ug", "Uc"]
    caret_r = ["Ra", "Rg", "Rc"]
    c1 = getRandomCaretAux(states, length - 1, level + 1)
    if level == 0:
        choice = random.randint(1, 4)
        if choice == 1:
            return f"E[ True Ug {c1}]"
        elif choice == 2:
            return f"E[ False Rg {c1}]"
        elif choice == 3:
            return f"A[ False Rg {c1}]"
        elif choice == 4:
            return f"A[ True Ug {c1}]"

    if random.randint(0, 1) == 1:
        s = states[random.randint(0, len(states) - 1)]
    else:
        s = "!" + states[random.randint(0, len(states) - 1)]

    choice = random.randint(1, 4)
    if choice == 1:
        op = caret_u[random.randint(0, 2)]
        return f"{s} && E[ True {op} {c1}]"
    elif choice == 2:
        op = caret_u[random.randint(0, 1)]
        return f"{s} && A[ True {op} {c1}]"
    elif choice == 3:
        op = caret_r[random.randint(0, 2)]
        return f"{s} && E[ False {op} {c1}]"
    elif choice == 4:
        op = caret_r[random.randint(0, 1)]
        return f"{s} && A[ False {op} {c1}]"


def getRandomCaret(smpds, length):

    (states, alphabet, rules, smrules) = smpds
    s = states
    c = getRandomCaretAux(s, length)
    return c


import csv
import resource
import time


def createRandomSmpdsFile(
    state_size, alphabet_size, num_rules, num_smrules, caret_size
):
    smpds, init = generatePDS(state_size, alphabet_size, num_rules, num_smrules)
    caret = getRandomCaret(smpds, caret_size)
    print(caret)
    json_name = "test.json"
    with open(json_name, "w") as file:

        def set_default(obj):
            if isinstance(obj, frozenset) or isinstance(obj, set):
                return list(obj)
            print(type(obj))
            raise TypeError

        res = [smpds, caret, init, []]
        json.dump(res, file, default=set_default)

    return json_name, [num_rules, num_smrules, caret_size]


def proc_output(stdout, stderr, killed, max_mem, timeout, default_time):
    time_reg = re.compile(r"Time took: ([\d\.]*)s")
    col = [None] * 3
    kill_text = "" if not killed else "TIMEOUT of {}s".format(timeout)
    res = None
    if "True" in stdout:
        res = "True"
    if "False" in stdout:
        res = "False"

    err_text = ""
    if res == None:
        err_text = kill_text if killed else stderr.strip().split("\n")[-1]

    m = time_reg.search(stdout)
    if m == None:
        m = time_reg.search(stderr)
    # if m == None:
    #     raise Exception(('cannot find time took', stdout, stderr))

    col[0] = err_text
    col[1] = m.group(1) if m != None else default_time
    col[2] = max_mem

    return col


def test_equivalence(
    state_size, alphabet_size, num_rules, num_smrules, caret_size, trial
):
    ctl_json_name, stat = createRandomSmpdsFile(
        state_size, alphabet_size, num_rules, num_smrules, caret_size
    )

    col = [None] * 6
    timeout = 60 * 60

    last_err = ""
    with subprocess.Popen(
        ["./bcaret_mc_smpds", ctl_json_name, "-pytest"],
        text=True,
        stdin=subprocess.PIPE,
        stderr=subprocess.PIPE,
        stdout=subprocess.PIPE,
    ) as proc1:
        max_mem = 0
        stdout = ""
        killed = False
        start_time = time.time()
        last_out, last_err = "", ""
        while True:
            if time.time() - start_time > timeout:
                proc1.terminate()
                killed = True
                # proc1.kill()

            p = subprocess.Popen(
                ["grep", "VmRSS", "/proc/%s/status" % proc1.pid],
                shell=False,
                stdout=subprocess.PIPE,
                text=True,
            )
            s = p.communicate()[0]
            find = re.search(r"\d+", s)
            if s != None and find != None:
                curUsage = int(find.group())
                max_mem = max(max_mem, curUsage)

            try:
                last_out, last_err = proc1.communicate(timeout=0.1)
                break
            except subprocess.TimeoutExpired:
                pass

        stdout, stderr = last_out, last_err
        if len(stderr) < 1:
            last_err = stderr

        col[:3] = proc_output(
            stdout, stderr, killed, max_mem, timeout, time.time() - start_time
        )

    res_vals = set()
    with subprocess.Popen(
        ["./bcaret_mc_smpds", ctl_json_name, "-pytest", "-naive"],
        text=True,
        stdin=subprocess.PIPE,
        stderr=subprocess.PIPE,
        stdout=subprocess.PIPE,
    ) as proc1:
        max_mem = 0
        stdout = ""
        killed = False
        start_time = time.time()
        last_out, last_err = "", ""
        while True:
            if time.time() - start_time > timeout:
                proc1.terminate()
                killed = True
                break

            p = subprocess.Popen(
                ["grep", "VmRSS", "/proc/%s/status" % proc1.pid],
                shell=False,
                stdout=subprocess.PIPE,
                text=True,
            )
            s = p.communicate()[0]
            find = re.search(r"\d+", s)
            if s != None and find != None:
                curUsage = int(find.group())
                max_mem = max(max_mem, curUsage)

            try:
                last_out, last_err = proc1.communicate(timeout=0.1)
                break
            except subprocess.TimeoutExpired:
                pass

        stdout, stderr = last_out, last_err

        col[3:] = proc_output(
            stdout, stderr, killed, max_mem, timeout, time.time() - start_time
        )

    csv_file = "results_stat_single.csv"
    col = stat + col + [trial]
    with open(csv_file, "a") as f:
        writer = csv.writer(f)
        writer.writerow(col)


import math

if __name__ == "__main__":
    subprocess.call(["sh", "./build.sh"])

    done = []

    for trial in range(200):
        for num_rules in [100, 200, 300, 400]:
            for num_smrules in [20, 10, 15]:
                for caret_size in [3, 5, 7]:
                    if [num_rules, num_smrules, caret_size] in done:
                        continue
                    h = hashlib.new("sha256")
                    h.update(f"{num_rules}:{num_smrules}:{caret_size}".encode())
                    seed = int(h.hexdigest()[:15], 16)
                    random.seed(seed)
                    state_size = int(math.sqrt(num_rules))
                    alphabet_size = random.randint(
                        int((num_rules // state_size) // 2),
                        int(num_rules // state_size),
                    )
                    print(num_rules, num_smrules, caret_size)
                    test_equivalence(
                        state_size,
                        alphabet_size,
                        num_rules,
                        num_smrules,
                        caret_size,
                        trial,
                    )
