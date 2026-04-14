/**
 * QCAL ∞³ Dashboard - Frontend JavaScript
 * ========================================
 * 
 * Real-time updates and interaction for QCAL dashboard
 * Frequency: 141.7001 Hz
 */

// Configuration
const UPDATE_INTERVAL = 5000; // 5 seconds
const COHERENCE_TARGET = 244.36;

// State
let updateTimer = null;

/**
 * Fetch and update system status
 */
async function updateSystemStatus() {
    try {
        const response = await fetch('/api/status');
        const data = await response.json();
        
        const statusDiv = document.getElementById('system-status');
        
        const beaconStatus = data.beacon === 'active' ? 
            '<span class="status-badge status-active">Active</span>' :
            '<span class="status-badge status-error">Missing</span>';
        
        const timestamp = new Date(data.timestamp).toLocaleTimeString();
        
        statusDiv.innerHTML = `
            <div class="metric">
                <span class="metric-label">Beacon</span>
                ${beaconStatus}
            </div>
            <div class="metric">
                <span class="metric-label">Frequency</span>
                <span class="metric-value">${data.frequency} Hz</span>
            </div>
            <div class="metric">
                <span class="metric-label">Target Coherence</span>
                <span class="metric-value">${data.coherence_target}</span>
            </div>
            <div class="metric">
                <span class="metric-label">Last Update</span>
                <span class="metric-value">${timestamp}</span>
            </div>
        `;
    } catch (error) {
        console.error('Error updating system status:', error);
        document.getElementById('system-status').innerHTML = 
            '<div class="status-badge status-error">Connection Error</div>';
    }
}

/**
 * Fetch and update coherence data
 */
async function updateCoherence() {
    try {
        const response = await fetch('/api/coherence');
        const data = await response.json();
        
        const coherenceDiv = document.getElementById('coherence-status');
        
        const current = data.current || 0;
        const percentage = Math.min((current / data.target) * 100, 100);
        
        const status = current >= data.target * 0.95 ? 'OPTIMAL' :
                      current >= data.target * 0.74 ? 'ACCEPTABLE' : 'CRITICAL';
        
        const statusClass = status === 'OPTIMAL' ? 'status-active' :
                           status === 'ACCEPTABLE' ? 'status-warning' : 'status-error';
        
        coherenceDiv.innerHTML = `
            <div class="metric">
                <span class="metric-label">Current</span>
                <span class="metric-value">${current.toFixed(2)}</span>
            </div>
            <div class="metric">
                <span class="metric-label">Target</span>
                <span class="metric-value">${data.target}</span>
            </div>
            <div class="coherence-bar">
                <div class="coherence-fill" style="width: ${percentage}%">
                    ${percentage.toFixed(1)}%
                </div>
            </div>
            <div class="metric">
                <span class="metric-label">Status</span>
                <span class="status-badge ${statusClass}">${status}</span>
            </div>
        `;
    } catch (error) {
        console.error('Error updating coherence:', error);
        document.getElementById('coherence-status').innerHTML = 
            '<div class="status-badge status-error">Connection Error</div>';
    }
}

/**
 * Fetch and update agent status
 */
async function updateAgents() {
    try {
        const response = await fetch('/api/agents');
        const agents = await response.json();
        
        const agentsDiv = document.getElementById('agents-status');
        
        let html = '<ul class="agent-list">';
        
        for (const [name, data] of Object.entries(agents)) {
            const displayName = name.split('_').map(w => 
                w.charAt(0).toUpperCase() + w.slice(1)
            ).join(' ');
            
            const statusClass = data.status === 'ready' ? 'status-ready' :
                               data.status === 'running' ? 'status-active' :
                               data.status === 'error' ? 'status-error' : 'status-warning';
            
            html += `
                <li class="agent-item">
                    <span>🤖 ${displayName}</span>
                    <span class="status-badge ${statusClass}">${data.status.toUpperCase()}</span>
                </li>
            `;
        }
        
        html += '</ul>';
        agentsDiv.innerHTML = html;
    } catch (error) {
        console.error('Error updating agents:', error);
        document.getElementById('agents-status').innerHTML = 
            '<div class="status-badge status-error">Connection Error</div>';
    }
}

/**
 * Update validation status
 */
async function updateValidation() {
    try {
        const response = await fetch('/api/status');
        const data = await response.json();
        
        const validationDiv = document.getElementById('validation-status');
        
        const v5Status = data.validation.v5_coronacion === 'available' ?
            '<span class="status-badge status-active">Available</span>' :
            '<span class="status-badge status-warning">Not Found</span>';
        
        const evacLines = data.validation.evac_rpsi_lines || 'N/A';
        
        validationDiv.innerHTML = `
            <div class="metric">
                <span class="metric-label">V5 Coronación</span>
                ${v5Status}
            </div>
            <div class="metric">
                <span class="metric-label">Evac_Rpsi Data</span>
                <span class="metric-value">${evacLines} lines</span>
            </div>
        `;
    } catch (error) {
        console.error('Error updating validation:', error);
    }
}

/**
 * Run V5 Coronación validation
 */
async function runValidation() {
    const button = document.getElementById('run-validation');
    const originalText = button.textContent;
    
    button.disabled = true;
    button.textContent = '⏳ Running validation...';
    
    try {
        const response = await fetch('/api/run_validation', {
            method: 'POST'
        });
        
        const result = await response.json();
        
        if (result.status === 'success') {
            button.textContent = '✅ Validation Complete!';
            setTimeout(() => {
                button.textContent = originalText;
                button.disabled = false;
            }, 3000);
        } else {
            button.textContent = `❌ ${result.status.toUpperCase()}`;
            setTimeout(() => {
                button.textContent = originalText;
                button.disabled = false;
            }, 3000);
        }
    } catch (error) {
        console.error('Error running validation:', error);
        button.textContent = '❌ Error';
        setTimeout(() => {
            button.textContent = originalText;
            button.disabled = false;
        }, 3000);
    }
}

/**
 * Update all dashboard components
 */
async function updateDashboard() {
    await Promise.all([
        updateSystemStatus(),
        updateCoherence(),
        updateAgents(),
        updateValidation()
    ]);
}

/**
 * Initialize dashboard
 */
function initDashboard() {
    console.log('🌌 QCAL ∞³ Dashboard initialized');
    console.log('📡 Frequency: 141.7001 Hz');
    
    // Initial update
    updateDashboard();
    
    // Set up periodic updates
    updateTimer = setInterval(updateDashboard, UPDATE_INTERVAL);
    
    // Set up validation button
    const validationButton = document.getElementById('run-validation');
    if (validationButton) {
        validationButton.addEventListener('click', runValidation);
    }
}

// Initialize when DOM is ready
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', initDashboard);
} else {
    initDashboard();
}

// Cleanup on page unload
window.addEventListener('beforeunload', () => {
    if (updateTimer) {
        clearInterval(updateTimer);
    }
});
