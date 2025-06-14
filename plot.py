import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path

# Everything
all = {'Road': 37.3, 'Road Shuffled': 37.4, 'Page Link': 31.5, 'Page Link Shuffled': 31.4}
# No parallelism
join = {'Road': 103.1, 'Road Shuffled': 98.2, 'Page Link': 91.2, 'Page Link Shuffled': 83.4}
# No join
index = {'Road': 103.4, 'Road Shuffled': 179.9, 'Page Link': 104.9, 'Page Link Shuffled': 98.1}
# Nothing
nothing = {'Road': 103.8, 'Road Shuffled': float("inf"), 'Page Link': 111.3, 'Page Link Shuffled': 109.9}

cats = ['Road', 'Road Shuffled', 'Page Link', 'Page Link Shuffled']
arrs = []
for data in [all, join, index, nothing]:
    arr = []
    for v in cats:
        arr.append(data[v])
    arrs.append(arr)


w, x = 0.2, np.arange(len(cats))
displacement = -1.5 * w
for v, hat, col, desc in zip(reversed(arrs), ['/', '\\\\', '//', '\\'], ['#7173A9', "#E8AA78", "#A4BF7F", '#629DDD'], reversed(['Parallel', 'Join Optimization', 'Index Selection', 'Baseline'])):
    plt.bar(x + displacement, v, w, hatch=hat, color = col, label=desc)
    displacement += w


plt.xticks(x, cats)
plt.ylabel('Time (s)')
plt.title('Interpretation Time')
plt.legend()
plt.show()
