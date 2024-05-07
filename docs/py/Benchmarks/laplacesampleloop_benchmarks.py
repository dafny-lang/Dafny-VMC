import timeit
import secrets
import numpy
import matplotlib.pyplot as plt
from decimal import Decimal
import DafnyVMC
from diffprivlib.mechanisms import GaussianDiscrete
import discretegauss
from datetime import datetime
import tqdm

vmc_mean = []
vmc_std = []

fig,ax1 = plt.subplots()

rng = secrets.SystemRandom()
r = DafnyVMC.Random()

sigmas = []
for epsilon_times_100 in tqdm.tqdm(range(1, 500, 2)):
    vmc = []

    # The GaussianDiscrete class does not expose the sampler directly, and needs to be instantiated with `(epsilon, delta)`.
    # We access its `_scale` member to get the values `sigma`'s needed by `DafnyVMC` and `discretegauss`.
    g = GaussianDiscrete(epsilon=0.01 * epsilon_times_100, delta=0.00001)
    sigma = g._scale
    sigmas += [sigma]

    sigma_num, sigma_denom = Decimal(sigma).as_integer_ratio()
    sigma_squared = sigma ** 2

    for i in range(1100):
        start_time = timeit.default_timer()
        r.DiscreteLaplaceSampleLoop(sigma_num, sigma_denom)
        elapsed = timeit.default_timer() - start_time
        vmc.append(elapsed)

    vmc = numpy.array(vmc[-1000:])

    vmc_mean.append(vmc.mean()*1000.0)
    vmc_std.append(vmc.std()*1000.0)

ax1.plot(sigmas, vmc_mean, color='green', linewidth=1.0, label='VMC')
ax1.fill_between(sigmas, numpy.array(vmc_mean)-0.5*numpy.array(vmc_std), numpy.array(vmc_mean)+0.5*numpy.array(vmc_std),
    alpha=0.2, facecolor='k',
    linewidth=2, linestyle='dashdot', antialiased=True)

ax1.set_xlabel("Sigma")
ax1.set_ylabel("Sampling Time (ms)")
plt.legend(loc = 'best')
now = datetime.now()
filename = 'LaplaceSampleLoopBenchmarks' + now.strftime("%H%M%S") + '.pdf'
plt.savefig(filename)