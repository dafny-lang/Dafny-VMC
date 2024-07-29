import matplotlib.pyplot as plt
import secrets
from decimal import Decimal
from datetime import datetime
import DafnyVMC
import discretegauss
from diffprivlib.mechanisms import GaussianDiscrete

fig, axs = plt.subplots(8, 3, figsize=(20, 20))

rng = secrets.SystemRandom()
r = DafnyVMC.Random()

for i in range(8):
    vmc_data = []
    ibm_dgdp_data = []
    ibm_dpl_data = []

    epsilon_times_100 = 1 + (i**2)*2.5
    g = GaussianDiscrete(epsilon=0.01 * epsilon_times_100, delta=0.00001)

    sigma = g._scale
    sigma_squared = sigma ** 2
    sigma_num, sigma_denom = Decimal(sigma).as_integer_ratio()

    title_vmc = 'VMC, Sigma = ' + str(sigma)
    title_ibm_dgdp = 'IBM-DGDP, Sigma = ' + str(sigma)
    title_ibm_dpl = 'IBM-DPL, Sigma = ' + str(sigma)

    for _ in range(100000):
        vmc_data.append(r.DiscreteGaussianSample(sigma_num, sigma_denom))
        ibm_dgdp_data.append(discretegauss.sample_dgauss(sigma_squared, rng))
        ibm_dpl_data.append(g.randomise(0))

    axs[i, 0].hist(vmc_data, color='lightgreen', ec='black', bins=50)
    axs[i, 0].set_title(title_vmc)
    axs[i, 1].hist(ibm_dgdp_data, color='lightgreen', ec='black', bins=50)
    axs[i, 1].set_title(title_ibm_dgdp)
    axs[i, 2].hist(ibm_dpl_data, color='lightgreen', ec='black', bins=50)
    axs[i, 2].set_title(title_ibm_dpl)

now = datetime.now()
filename = 'GaussianDiagrams' + now.strftime("%H%M%S") + '.pdf'
plt.subplots_adjust(wspace=0.4, hspace=0.4)
plt.savefig(filename)