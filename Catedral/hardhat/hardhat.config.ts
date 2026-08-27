import { HardhatUserConfig } from "hardhat/config";
import "@nomicfoundation/hardhat-toolbox";
import "@nomicfoundation/hardhat-verify";
import * as dotenv from "dotenv";
dotenv.config();
const PRIVATE_KEY = process.env.PRIVATE_KEY || "0x" + "0".repeat(64);
const ALCHEMY_API_KEY = process.env.ALCHEMY_API_KEY || "";
const config: HardhatUserConfig = {
  solidity: { version: "0.8.19", settings: { optimizer: { enabled: true, runs: 200 } } },
  networks: {
    hardhat: { chainId: 31337 },
    localhost: { url: "http://127.0.0.1:8545" },
    sepolia: { url: `https://eth-sepolia.g.alchemy.com/v2/${ALCHEMY_API_KEY}`, accounts: [PRIVATE_KEY], chainId: 11155111 },
    mumbai: { url: `https://polygon-mumbai.g.alchemy.com/v2/${ALCHEMY_API_KEY}`, accounts: [PRIVATE_KEY], chainId: 80001 },
    polygon: { url: `https://polygon-mainnet.g.alchemy.com/v2/${ALCHEMY_API_KEY}`, accounts: [PRIVATE_KEY], chainId: 137 },
  },
  etherscan: { apiKey: { sepolia: process.env.ETHERSCAN_API_KEY || "", polygon: process.env.POLYGONSCAN_API_KEY || "" } },
};
export default config;
