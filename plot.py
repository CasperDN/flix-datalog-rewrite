import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path

# Everything
all = {'Road': 37.1, 'Road Shuffled': 37.1, 'Page Link': 31.4, 'Page Link Shuffled': 31.4}
# No parallelism
join = {'Road': 81.9, 'Road Shuffled': 76.0, 'Page Link': 70.3, 'Page Link Shuffled': 63.4}
# No join
index = {'Road': 83.2, 'Road Shuffled': 128, 'Page Link': 80.5, 'Page Link Shuffled': 81.3}
# Nothing
nothing = {'Road': 83.9, 'Road Shuffled': float("inf"), 'Page Link': 81.4, 'Page Link Shuffled': 81.3}

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
