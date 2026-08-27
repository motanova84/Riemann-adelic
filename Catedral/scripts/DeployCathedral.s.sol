// SPDX-License-Identifier: MIT
// ═══════════════════════════════════════════════════════════════════════════════
// CATEDRAL πCODE v7.1 — DEPLOYMENT SCRIPT (Foundry)
// forge script scripts/DeployCathedral.s.sol --rpc-url sepolia --broadcast -vvvv
// ═══════════════════════════════════════════════════════════════════════════════

pragma solidity ^0.8.19;

import "forge-std/Script.sol";
import "../src/PiCodeSpectralCathedral.sol";

contract DeployCathedralScript is Script {
    function setUp() public {}

    function run() public {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(deployerPrivateKey);
        
        console.log("═══════════════════════════════════════════════════════════════");
        console.log(" CATEDRAL πCODE v7.1 — FOUNDRY DEPLOYMENT");
        console.log(" Frecuencia: 141.7001 Hz");
        console.log("═══════════════════════════════════════════════════════════════");
        console.log(" Deployer:", deployer);

        vm.startBroadcast(deployerPrivateKey);
        PiCodeSpectralCathedral cathedral = new PiCodeSpectralCathedral();
        vm.stopBroadcast();

        address actualDeployer = cathedral.director();
        console.log(" Director:", actualDeployer);
        console.log(" Catedral activa:", cathedral.cathedralActive());
        console.log(" Posiciones totales:", cathedral.totalPositions());
        console.log(" Liquidez total:", cathedral.totalLiquidity());

        // Verify spectral states
        console.log("\n[✓] Verificando estados espectrales...");
        uint256[13] memory expectedMagnitudes = [
            1118034, 2003902, 3000514, 4000122, 5000040,
            6000016, 7000007, 8000004, 9000002, 10000001,
            11000001, 12000001, 13000000
        ];
        for (uint8 n = 0; n < 13; n++) {
            (uint8 stateN, uint256 magnitude,,, , string memory interpretation) = cathedral.spectralStates(n);
            bool valid = (magnitude == expectedMagnitudes[n]);
            console.log(valid ? "[OK]" : "[FAIL]", "n=", n, "|E_n|=", magnitude, interpretation);
        }

        // Guardian pulse
        console.log("\n[✓] Emitiendo pulso Guardian...");
        vm.startBroadcast(deployerPrivateKey);
        cathedral.emitGuardianPulse();
        vm.stopBroadcast();
        console.log(" Coherencia:", cathedral.computeSystemCoherence());

        console.log("\n═══════════════════════════════════════════════════════════════");
        console.log(" DESPLIEGUE COMPLETADO");
        console.log("═══════════════════════════════════════════════════════════════");
        console.log(" Direccion:", address(cathedral));
        console.log(" Director:", cathedral.director());
        console.log(" Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ");
    }
}
