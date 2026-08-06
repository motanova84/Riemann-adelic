// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
import "forge-std/Script.sol";
import "../src/PiCodeSpectralCathedral.sol";
contract DeployCathedral is Script {
  function run() external {
    uint256 pk = vm.envUint("PRIVATE_KEY");
    address deployer = vm.addr(pk);
    vm.startBroadcast(pk);
    PiCodeSpectralCathedral cathedral = new PiCodeSpectralCathedral();
    vm.stopBroadcast();
    console.log("Catedral:", address(cathedral));
    console.log("Director:", cathedral.director());
    uint256[13] memory exp = [1118034,2003902,3000514,4000122,5000040,6000016,7000007,8000004,9000002,10000001,11000001,12000001,13000000];
    for (uint8 n = 0; n < 13; n++) {
      (uint8 sn, uint256 mag,,,, string memory interp) = cathedral.spectralStates(n);
      console.log(mag == exp[n] ? "[OK]" : "[FAIL]", "n=", n, "|E_n|=", mag, interp);
    }
    vm.startBroadcast(pk);
    cathedral.emitGuardianPulse();
    vm.stopBroadcast();
    console.log("Coherencia:", cathedral.computeSystemCoherence());
    console.log("∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ");
  }
}
