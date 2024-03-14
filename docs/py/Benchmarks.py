import timeit
import secrets
import numpy
import matplotlib.pyplot as plt
from decimal import Decimal
import DafnyVMC
from IBM import sample_dgauss
from datetime import datetime

sigma_range = 100
step = 1
sigmas = numpy.arange(0.000001, sigma_range, step).tolist()

vmc_mean = []
vmc_std = []
ibm_mean = []
ibm_std = []

fig,ax1 = plt.subplots()

r = DafnyVMC.Random()

for sigma in sigmas:
    vmc = []
    ibm = []
    sigma_num, sigma_denom = Decimal(sigma).as_integer_ratio()
    sigma_squared = sigma ** 2

    for i in range(1100):
        start_time = timeit.default_timer()
        r.DiscreteGaussianSample(sigma_num, sigma_denom)
        elapsed = timeit.default_timer() - start_time
        vmc.append(elapsed)

    for i in range(1100):
        start_time = timeit.default_timer()
        sample_dgauss(sigma_squared, rng=secrets.SystemRandom())
        elapsed = timeit.default_timer() - start_time
        ibm.append(elapsed)

    vmc = numpy.array(vmc[-1000:])
    ibm = numpy.array(ibm[-1000:])

    vmc_mean.append(vmc.mean()*1000.0)
    vmc_std.append(vmc.std()*1000.0)
    ibm_mean.append(ibm.mean()*1000.0)
    ibm_std.append(ibm.std()*1000.0)

ax1.plot(sigmas, vmc_mean, color='green', linewidth=1.0, label='VMC')
ax1.fill_between(sigmas, numpy.array(vmc_mean)-0.5*numpy.array(vmc_std), numpy.array(vmc_mean)+0.5*numpy.array(vmc_std),
    alpha=0.2, facecolor='k',
    linewidth=2, linestyle='dashdot', antialiased=True)

ax1.plot(sigmas, ibm_mean, color='red', linewidth=1.0, label='IBM')
ax1.fill_between(sigmas, numpy.array(ibm_mean)-0.5*numpy.array(ibm_std), numpy.array(ibm_mean)+0.5*numpy.array(ibm_std),
    alpha=0.2,  facecolor='y',
    linewidth=2, linestyle='dashdot', antialiased=True)

ax1.set_xlabel("Sigma")
ax1.set_ylabel("Sampling Time (ms)")
plt.legend(loc = 'best')
now = datetime.now()
filename = 'Benchmarks' + now.strftime("%H_%M_%S") + '.pdf'
plt.savefig(filename)