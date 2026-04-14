# 🌐 Riemann-Adelic Web Interface

## Overview

This repository includes two web interfaces:

1. **Next.js Dashboard** (NEW) - Modern, interactive dashboard for exploring the Riemann Hypothesis proof
2. **API Server** - Backend API for mathematical computations and validations

## Next.js Dashboard (Recommended)

### 🎨 Modern Interactive Interface

A beautiful, responsive dashboard built with Next.js 14, TypeScript, and Tailwind CSS.

**Features:**
- Real-time proof status and validation results
- Interactive cards displaying key information
- Optimized Geist fonts for professional typography
- Responsive design for all devices
- Spanish language interface

### Quick Start

```bash
# Install dependencies
npm install

# Start development server
npm run dev
```

Open [http://localhost:3000](http://localhost:3000) in your browser.

### Documentation

See [NEXTJS_README.md](NEXTJS_README.md) for complete documentation and [QUICKSTART_NEXTJS.md](QUICKSTART_NEXTJS.md) for quick reference.

---

## API Server (Legacy)

This web interface provides an interactive demonstration of the enhanced mathematical functions implemented for the Riemann Hypothesis validation project.

## Enhanced Functions

### 📊 Function X (f1) - Enhanced Smooth Bump Function
- **Original**: Basic smooth bump function with `exp(-1/(1-u²/a²))`
- **Enhanced**: 
  - Improved numerical stability with conservative boundary handling
  - Added normalization factor for better integration properties
  - Additional smoothing factor: `exp(-x²/2)`
  - Better error handling for edge cases
  - Mathematical rigor improvements for critical line verification

### 🔬 A_∞ Function - Enhanced Archimedean Contribution
- **Original**: Basic archimedean integral computation
- **Enhanced**:
  - Better error handling for digamma function computation
  - Functional equation handling for negative real parts
  - Convergence factors for improved integration stability
  - Adaptive error control with fallback mechanisms
  - Enhanced normalization and real part extraction

## Running the Web Interface

### Prerequisites
```bash
# Install Node.js dependencies
npm install

# Install Python dependencies (if not already installed)
pip install -r requirements.txt
```

### Start the Server
```bash
# Start the Node.js web server
npm start

# Or for development with auto-reload
npm run dev
```

### Access the Interface
Open your browser and navigate to: `http://localhost:3000`

## API Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/` | GET | API information and available endpoints |
| `/health` | GET | System health check |
| `/functions` | GET | List of available mathematical functions |
| `/validate` | POST | Run Riemann Hypothesis validation |
| `/demo` | POST | Run critical line demonstration |
| `/test-f1` | POST | Test enhanced f1 function |

## Web Interface Features

### 🔬 Enhanced f1 Function Test
- Interactive testing of the improved f1 function
- Real-time output display
- Mathematical validation results

### ⚖️ Quick Validation
- Run Riemann Hypothesis validation with enhanced functions
- Configurable parameters (primes count, zeros count, test function)
- Arithmetic vs spectral side comparison

### 🎯 Critical Line Demo
- Demonstrate critical line verification under RH axioms
- Show that zeros satisfy Re(s) = 1/2
- Mathematical proof certificate generation

### 📊 System Status
- Real-time health monitoring
- Python environment validation
- Dependency status checking

## Example API Usage

### Run Validation
```javascript
const response = await fetch('/validate', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
        max_primes: 100,
        max_zeros: 100,
        test_function: 'f1'
    })
});
const result = await response.json();
```

### Test Enhanced f1 Function
```javascript
const response = await fetch('/test-f1', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' }
});
const result = await response.json();
```

## Mathematical Improvements Summary

1. **Numerical Stability**: Enhanced boundary conditions and error handling
2. **Convergence**: Better integration properties with normalization factors
3. **Precision**: Improved mathematical rigor for critical line verification
4. **Robustness**: Fallback mechanisms and adaptive error control
5. **Performance**: Optimized computations for web interface responsiveness

## Integration with Existing Workflows

The web interface is fully compatible with existing GitHub Actions workflows:
- Changes to `utils/mellin.py` trigger validation pipelines
- Package.json updates enable Node.js deployment capabilities
- Web interface provides real-time testing of mathematical functions

## Deployment Options

### Local Development
```bash
npm run dev
```

### Production Deployment
```bash
npm start
```

### Docker (Optional)
```dockerfile
FROM node:18-alpine
WORKDIR /app
COPY package*.json ./
RUN npm install --production
COPY . .
EXPOSE 3000
CMD ["npm", "start"]
```

## Contributing

When making changes to the mathematical functions:

1. Update the functions in `utils/mellin.py`
2. Test using `python test_function_updates.py`
3. Test the web interface at `http://localhost:3000`
4. Ensure GitHub Actions workflows pass
5. Update documentation as needed

## Support

For mathematical questions: José Manuel Mota Burruezo (motanova84@gmail.com)
For technical issues: Open an issue in the GitHub repository