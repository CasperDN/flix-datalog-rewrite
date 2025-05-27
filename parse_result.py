import typing


def read(fileName, descNum):
    dic = []
    with open(fileName) as f:
        f.readline()
        while(True):
            resetPoint = f.tell()
            if(f.readline() == ""):
                break
            else:
                f.seek(resetPoint)

            desc = parse_desc(f, descNum)
            avg = parse_vec(f)
            dic.append((desc, avg))
    return dic



def parse_vec(f: typing.TextIO):
    line: str = f.readline()
    vals = line
    if(line[0] == "V"):
        vals = line[8:-2]
    values = vals.replace(' ', '').split(',')
    s = 0
    for v in values:
        s += int(v)
    return int(s / len(values))

def parse_desc(f: typing.TextIO, descNum):
    count = 0
    desc = []
    while(count < descNum):
        line: str = f.readline()
        split = line.replace(' ', '').replace('\n', '').split(':')
        key = split[0]
        val = int(split[1])
        desc.append((key, val))
        count = count + 1
    return desc

def satisfy(tuple, key, val):
    desc, _ = tuple

    return any(k == key and v == val for k, v in desc)

def filter_list(dic, key, val):
    return filter(lambda x: satisfy(x, key, val), dic)

res = read("C:/Users/caspe/OneDrive/Skrivebord/Uni/Speciale/Results/OrderExperiment.txt", 3)

res = filter_list(filter_list(res, "Threads", 32), "Insertions", 1000000)

for v in res:
    print(v)
# print(res.)