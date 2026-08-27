// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "forge-std/Test.sol";
import "../src/PiCodeSpectralCathedral.sol";

contract CathedralTest is Test {
    PiCodeSpectralCathedral public cathedral;
    address public director;
    address public user1;
    address public user2;
    uint256 constant F0 = 1417001;
    uint256 constant TAU_C = 999999;

    function setUp() public {
        director = address(this);
        user1 = makeAddr("user1");
        user2 = makeAddr("user2");
        vm.deal(user1, 100 ether);
        vm.deal(user2, 100 ether);
        cathedral = new PiCodeSpectralCathedral();
    }

    function testConstants() public {
        assertEq(cathedral.F0(), F0);
        assertEq(cathedral.TAU_C(), TAU_C);
        assertEq(cathedral.SPECTRAL_STATES(), 13);
    }

    function testSpectralStates() public {
        uint256[13] memory expected = [1118034, 2003902, 3000514, 4000122, 5000040,
            6000016, 7000007, 8000004, 9000002, 10000001, 11000001, 12000001, 13000000];
        for (uint8 n = 0; n < 13; n++) {
            (uint8 stateN, uint256 magnitude,,,,) = cathedral.spectralStates(n);
            assertEq(stateN, n);
            assertEq(magnitude, expected[n]);
        }
    }

    function testCreatePosition() public {
        vm.prank(user1);
        bytes32 contractId = cathedral.createPosition{value: 1 ether}(0, 30);
        assertEq(cathedral.totalPositions(), 1);
    }

    function testGuardianPulse() public {
        vm.prank(director);
        cathedral.emitGuardianPulse();
    }

    function testFuzzCreatePosition(uint8 state, uint8 lockDays, uint256 amount) public {
        vm.assume(amount >= 0.01 ether && amount <= 10 ether);
        vm.assume(state <= 12);
        vm.assume(lockDays >= 1 && lockDays <= 1825);
        vm.prank(user1);
        cathedral.createPosition{value: amount}(state, lockDays);
    }
}
