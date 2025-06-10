import typing
# import matplotlib.pyplot as plt

loop_num = 5

def read(fileName, withJoin):
    dic = {}
    with open(fileName) as f:
        while(True):
            resetPoint = f.tell()
            if(f.readline() == ""):
                break
            else:
                f.seek(resetPoint)

            desc = parse_desc(f)
            values = []
            for _ in range(0, loop_num):
                values.append(parse_times(f, withJoin))
            f.readline()
            avg_ms = int(f.readline().lstrip(' ').split(' ')[0])
            f.readline()
            keys = values[0].keys()
            sums = {}
            for key in keys:
                sums[key] = sum(map(lambda x: x[key], values))
            avgs = {k: v / loop_num for k, v in sums.items()}
            dic[desc] = avgs | {"avg_ms": avg_ms}

    return dic

def parse_times(f: typing.TextIO, withJoin: bool):
    start = readTime(f)
    res = {"start": start}
    if(withJoin):
        join_start_inter = readTime(f)
        join_end_inter = readTime(f)
        res = res | {"join_time": join_end_inter - join_start_inter}
    start_inter = readTime(f)
    end_inter = readTime(f)
    return res | {"inter_time": end_inter - start_inter, "compile_time": start_inter - start}

def readTime(f: typing.TextIO):
    return int(f.readline().replace(' ', '').replace('\n', '').split(':')[1])

def parse_desc(f: typing.TextIO):
    return f.readline().replace(' ', '').replace('\n', '').split(':')[1]


def satisfy(tuple, key, val):
    desc, _ = tuple
    return any(k == key and v == val for k, v in desc)

def filter_list(dic, key, val):
    return filter(lambda x: satisfy(x, key, val), dic)

# def plot(data, title, x_label, x_ticks):
#     colors = ["red", "blue", "green", "purple"]
#     for solver, color in zip(data.keys(), colors):
#         x = 0
#         y = 0
#         plt.plot(x, y, "o", label=solver, color=color)
#     plt.xlabel(x_label)
#     plt.ylabel("Time [ms]")
#     plt.title(title)
#     plt.xticks(x_ticks)
#     plt.legend()
#     plt.grid()
#     plt.show()

# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Index_selection/test.txt", False)
# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/flix-datalog-rewrite/_t.txt", True)
# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Join_optimization/WithJoin.txt", True)
res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Parallelism/NoPar.txt", True)


# Old
{
 'Road': 
 {'join_time': 14074.8, 'inter_time': 81852.4, 'compile_time': 26826.8, 'avg_ms': 39476},
 'PageLink': 
 {'join_time': 1577.8, 'inter_time': 70285.8, 'compile_time': 12368.4, 'avg_ms': 33314},
 'RoadShuffled': 
 {'join_time': 13162.8, 'inter_time': 76028.8, 'compile_time': 26335.4, 'avg_ms': 38996},
 'PageLinkShuffled': 
 {'join_time': 788.8, 'inter_time': 63366.0, 'compile_time': 11736.0, 'avg_ms': 31838}
}

# With join / no par (new)
{'Road':
 {'join_time': 16167.4, 'inter_time': 101702.4, 'compile_time': 18718.6, 'avg_ms': 43020},
 'PageLink':
 {'join_time': 1634.0, 'inter_time': 89249.4, 'compile_time': 10462.4, 'avg_ms': 36831},
 'RoadShuffled':
 {'join_time': 16245.2, 'inter_time': 97221.0, 'compile_time': 18313.8, 'avg_ms': 41601},
 'PageLinkShuffled':
 {'join_time': 822.0, 'inter_time': 83467.4, 'compile_time': 9713.8, 'avg_ms': 35206}
}

# Without join
{
 'Road': 
 {'inter_time': 84672.2, 'compile_time': 2198.0, 'avg_ms': 36582},
 'PageLink': 
 {'inter_time': 80672.8, 'compile_time': 7266.0, 'avg_ms': 34112},
 'RoadShuffled': 
 {'inter_time': 128481.6, 'compile_time': 1647.6, 'avg_ms': 44587},
 'PageLinkShuffled': 
 {'inter_time': 72610.0, 'compile_time': 6992.8, 'avg_ms': 32366}
}

# res = filter_list(res, "Insertions", 10000)


print(res)

# for v in res:
#     print(v)
# print(res.)