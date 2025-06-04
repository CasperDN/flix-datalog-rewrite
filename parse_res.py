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
            avg_ms = int(f.readline().split(' ')[0]) / loop_num
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

res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Index_selection/test.txt", False)

# res = filter_list(filter_list(res, "Order", 64), "Insertions", 10000)


# res = filter_list(res, "Insertions", 10000)


print(res)

# for v in res:
#     print(v)
# print(res.)