// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
import "forge-std/Test.sol";
import "../src/PiCodeSpectralCathedral.sol";
contract CathedralTest is Test {
  PiCodeSpectralCathedral cathedral;
  address user1 = makeAddr("user1");
  function setUp() public { cathedral = new PiCodeSpectralCathedral(); }
  function testConstants() public { assertEq(cathedral.SPECTRAL_STATES(), 13); assertTrue(cathedral.cathedralActive()); }
  function testSpectralStates() public {
    uint256[13] memory exp = [1118034,2003902,3000514,4000122,5000040,6000016,7000007,8000004,9000002,10000001,11000001,12000001,13000000];
    for (uint8 n = 0; n < 13; n++) {
      (uint8 sn, uint256 mag,,,,) = cathedral.spectralStates(n);
      assertEq(sn, n); assertEq(mag, exp[n]);
    }
  }
  function testCreatePosition() public {
    vm.deal(user1, 1 ether);
    vm.prank(user1);
    bytes32 cid = cathedral.createPosition{value: 1 ether}(0, 30);
    assertEq(cathedral.totalPositions(), 1);
  }
  function testGuardianPulse() public { cathedral.emitGuardianPulse(); }
  function testFuzz(uint8 state, uint256 amount) public {
    vm.assume(state < 13 && amount > 0 && amount <= 10 ether);
    vm.deal(user1, amount); vm.prank(user1);
    cathedral.createPosition{value: amount}(state, 30);
  }
}
