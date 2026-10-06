import { ethers, network } from "hardhat";
import * as fs from "fs";

async function main() {
  console.log("═══════════════════════════════════════════════════════════════");
  console.log(" CATEDRAL πCODE v7.1 — HARDHAT DEPLOYMENT");
  console.log(" Frecuencia: 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ");
  console.log("═══════════════════════════════════════════════════════════════");
  console.log(` Red: ${network.name} (Chain ID: ${network.config.chainId})`);
  
  const [deployer] = await ethers.getSigners();
  console.log(` Deployer: ${deployer.address}`);
  
  const Cathedral = await ethers.getContractFactory("PiCodeSpectralCathedral");
  const cathedral = await Cathedral.deploy();
  await cathedral.waitForDeployment();
  const cathedralAddress = await cathedral.getAddress();
  
  // Verify spectral states
  console.log("\n[✓] Verificando estados espectrales...");
  const expectedMagnitudes = [
    1118034, 2003902, 3000514, 4000122, 5000040,
    6000016, 7000007, 8000004, 9000002, 10000001,
    11000001, 12000001, 13000000
  ];
  for (let n = 0; n < 13; n++) {
    const state = await cathedral.spectralStates(n);
    const valid = state.magnitude === BigInt(expectedMagnitudes[n]);
    console.log(` ${valid ? "[OK]" : "[FAIL]"} n=${n} |E_n|=${state.magnitude} ${state.interpretation}`);
  }
  
  // Guardian pulse
  console.log("\n[✓] Emitiendo pulso Guardian...");
  const tx = await cathedral.emitGuardianPulse();
  await tx.wait();
  const coherence = await cathedral.computeSystemCoherence();
  console.log(` Coherencia del sistema: ${coherence}/10⁶`);
  
  // Summary
  console.log("\n═══════════════════════════════════════════════════════════════");
  console.log(" DESPLIEGUE COMPLETADO");
  console.log("═══════════════════════════════════════════════════════════════");
  console.log(` Dirección: ${cathedralAddress}`);
  console.log(` Director: ${deployer.address}`);
  console.log(` Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ`);
  
  // Save deployment
  const deployment = {
    network: network.name,
    chainId: network.config.chainId,
    contract: cathedralAddress,
    deployer: deployer.address,
    timestamp: Math.floor(Date.now() / 1000),
    f0: "141.7001 Hz",
    seal: "∴𓂀Ω∞³Φ"
  };
  const dir = "deployments";
  if (!fs.existsSync(dir)) fs.mkdirSync(dir);
  fs.writeFileSync(`${dir}/hardhat_${network.config.chainId}_cathedral_v7_1.json`, JSON.stringify(deployment, null, 2));
}

main().catch(console.error);
