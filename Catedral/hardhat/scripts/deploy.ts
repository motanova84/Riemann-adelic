import { ethers, run, network } from "hardhat";
async function main() {
  const [deployer] = await ethers.getSigners();
  console.log("═══════════════════════════════════════════════════════════════");
  console.log(" DEPLOYMENT CATEDRAL πCODE v7.1 — HARDHAT");
  console.log("═══════════════════════════════════════════════════════════════");
  console.log(` Network: ${network.name}`);
  console.log(` Chain ID: ${network.config.chainId}`);
  console.log(` Deployer: ${deployer.address}`);
  console.log(` Balance: ${ethers.formatEther(await deployer.provider!.getBalance(deployer.address))} ETH`);
  const CathedralFactory = await ethers.getContractFactory("PiCodeSpectralCathedral");
  console.log("[2/5] Desplegando contrato...");
  const cathedral = await CathedralFactory.deploy();
  await cathedral.waitForDeployment();
  const cathedralAddress = await cathedral.getAddress();
  console.log(`[✓] Contrato desplegado en: ${cathedralAddress}`);
  const expectedMagnitudes = [1118034n,2003902n,3000514n,4000122n,5000040n,6000016n,7000007n,8000004n,9000002n,10000001n,11000001n,12000001n,13000000n];
  for (let n = 0; n < 13; n++) {
    const state = await cathedral.spectralStates(n);
    const valid = state.E_n_magnitude === expectedMagnitudes[n];
    console.log(` ${valid ? "[OK]" : "[FAIL]"} n=${n} |E_n|=${state.E_n_magnitude} ${state.interpretation}`);
  }
  const tx = await cathedral.emitGuardianPulse();
  await tx.wait();
  console.log(` Coherencia: ${(await cathedral.computeSystemCoherence()).toString()}/10⁶`);
  console.log("═══════════════════════════════════════════════════════════════");
  console.log(" DESPLIEGUE COMPLETADO");
  console.log("═══════════════════════════════════════════════════════════════");
  console.log(` Dirección: ${cathedralAddress}`);
  console.log(` Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ`);
}
main().catch(console.error);
