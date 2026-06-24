import csv

import pandas

data = []
with open("results_stat_single.csv", "r") as f:
    reader = csv.reader(f)
    for row in reader:
        data.append(row[:9])

with open("results_df.csv", "w") as f:
    csv.writer(f).writerows(data)

tbl = pandas.read_csv(
    "results_df.csv",
    names=[
        "rules",
        "sm_rules",
        "closure",
        "smpds_err",
        "smpds_time",
        "smpds_mem",
        "pds_err",
        "pds_time",
        "pds_mem",
    ],
)
# tbl = tbl[tbl['smpds_err'].isnull() & tbl['pds_err'].isnull()]
tbl["speedup"] = tbl["pds_time"] / tbl["smpds_time"]


grouped = tbl.groupby(["rules", "sm_rules", "closure"])
agg = grouped.agg(
    smpds_time_mean=("smpds_time", "mean"),
    smpds_time_std=("smpds_time", "std"),
    smpds_mem_mean=("smpds_mem", "mean"),
    smpds_mem_std=("smpds_mem", "std"),
    pds_time_mean=("pds_time", "mean"),
    pds_time_std=("pds_time", "std"),
    pds_mem_mean=("pds_mem", "mean"),
    pds_mem_std=("pds_mem", "std"),
    speedup_median=("speedup", "median"),
    smpds_err=("smpds_err", "first"),
    pds_err=("pds_err", "first"),
)
res = agg.reset_index()

mem_filter = lambda x: (
    "{:.1f}G".format(float(x) / (1024 * 1024))
    if float(x) / (1024 * 1024) > 0.1
    else "{:.1f}M".format(float(x) / 1024)
)

out_tbl = res.copy()
result = []
for i, row in out_tbl.iterrows():
    res_row = [None] * 7
    res_row[0] = "{} + {}".format(int(row.rules), int(row.sm_rules))
    res_row[1] = "{}".format(int(row.closure))
    res_row[2] = "{:.1f} / {:.1f}".format(row.smpds_time_mean, row.smpds_time_std)
    res_row[3] = "{}".format(
        mem_filter(row.smpds_mem_mean), mem_filter(row.smpds_mem_std)
    )
    res_row[4] = "{:.1f} / {:.1f}".format(row.pds_time_mean, row.pds_time_std)
    res_row[5] = "{}".format(mem_filter(row.pds_mem_mean), mem_filter(row.pds_mem_std))
    res_row[6] = "{:.0f}".format(row.speedup_median)
    if not pandas.isnull(row.smpds_err):
        err = (
            f"{{\\color{{red}} \\textbf{{Timeout}} }}"
            if "TIMEOUT" in row.smpds_err
            else f"{{\\color{{red}} \\textbf{{OOM}} }}"
        )
        res_row[2] = err
        res_row[3] = "-"
        res_row[6] = "-"
    if not pandas.isnull(row.pds_err):
        err = (
            f"{{\\color{{red}} \\textbf{{Timeout}} }}"
            if "TIMEOUT" in row.pds_err
            else f"{{\\color{{red}} \\textbf{{OOM}} }}"
        )
        res_row[4] = err
        res_row[5] = "-"
        res_row[6] = "-"
    elif row.speedup_median > 30:
        res_row = [f"{{\\bf {d} }}" for d in res_row]

    result.append(" & ".join(res_row) + " \\\\ \\hline  \n")

txt = "".join(result)
print(txt)
