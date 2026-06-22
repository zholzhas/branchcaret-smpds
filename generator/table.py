import pandas
import csv

data = []
with open('results_stat.csv', 'r') as f:
    reader = csv.reader(f)
    for row in reader:
        data.append(row[:9])

with open('results_df.csv', 'w') as f:
    csv.writer(f).writerows(data)

tbl = pandas.read_csv('results_df.csv', names=['rules', 'sm_rules', 'closure', 'smpds_err', 'smpds_time', 'smpds_mem', 'pds_err', 'pds_time', 'pds_mem'])
tbl = tbl[tbl['smpds_err'].isnull() & tbl['pds_err'].isnull()]
tbl['speedup'] = tbl['pds_time'] / tbl['smpds_time']


grouped = tbl.drop(columns=['pds_err', 'smpds_err']).groupby(['rules', 'sm_rules', 'closure'])
agg = grouped.agg(
    smpds_time_mean=('smpds_time', 'mean'),
    smpds_time_std=('smpds_time', 'std'),
    smpds_mem_mean=('smpds_mem', 'mean'),
    smpds_mem_std=('smpds_mem', 'std'),
    pds_time_mean=('pds_time', 'mean'),
    pds_time_std=('pds_time', 'std'),
    pds_mem_mean=('pds_mem', 'mean'),
    pds_mem_std=('pds_mem', 'std'),
    speedup_median=('speedup', 'median'),
)
res = agg.reset_index()

mem_filter = lambda x: '{:.1f} GB'.format(float(x) / (1024 * 1024)) if float(x) / (1024 * 1024) > 1 else '{:.1f} MB'.format(float(x) / 1024)

out_tbl = res.copy()
result = []
for (i, row) in out_tbl.iterrows():
    res_row = [None] * 7
    res_row[0] = '{} + {}'.format(int(row.rules), int(row.sm_rules))
    res_row[1] = '{}'.format(int(row.closure))
    res_row[2] = '{:.1f}s $\\pm$ {:.1f}s'.format(row.smpds_time_mean, row.smpds_time_std)
    res_row[3] = '{} $\\pm$ {}'.format(mem_filter(row.smpds_mem_mean), mem_filter(row.smpds_mem_std))
    res_row[4] = '{:.1f}s $\\pm$ {:.1f}s'.format(row.pds_time_mean, row.pds_time_std)
    res_row[5] = '{} $\\pm$ {}'.format(mem_filter(row.pds_mem_mean), mem_filter(row.pds_mem_std))
    res_row[6] = '{:.1f}'.format(row.speedup_median)


    result.append(' & '.join(res_row) + ' \\hline \\\\ \n')

txt = ''.join(result)
print(txt)