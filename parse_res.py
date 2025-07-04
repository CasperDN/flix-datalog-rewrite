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
    end_marshall = readTime(f)
    return res | {"inter_time": end_inter - start_inter, "compile_time": start_inter - start, "marshall_time": end_marshall - end_inter, "total": end_marshall - start_inter}

def readTime(f: typing.TextIO):
    return int(f.readline().replace(' ', '').replace('\n', '').split(':')[1])

def parse_desc(f: typing.TextIO):
    return f.readline().replace(' ', '').replace('\n', '').split(':')[1]


def project(dictionary: dict, values):
    dic = {}
    for k, v in dictionary.items():
        innerDic = {}
        for i in values:
            if i in v:
                innerDic[i] = v[i]
        dic[k] = innerDic
    return dic


# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/B+_tree/Real/128__.txt", True)
# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Index_selection/NoIndex.txt", False)
# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/flix-datalog-rewrite/_t.txt", True)
# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Join_optimization/WithJoin.txt", True)
# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Parallelism/WithPar.txt", True)

# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/OldEngine/Res.txt", False)

# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Provenance/WithProv.txt", True)

# res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Stratification/PathFirst.txt", True)

res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/Inliner/All.txt", True)

# keptValues = ["join_time", "inter_time", "compile_time", "marshall_time", "total"]
# keptValues = ["compile_time", "inter_time", "marshall_time"]
# keptValues = ["inter_time"]




# res = project(res, keptValues)

# res = filter_list(res, "Insertions", 10000)


print(res)

# for v in res:
#     print(v)
# print(res.)