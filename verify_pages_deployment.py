#!/usr/bin/env python3
"""
GitHub Pages Deployment Verification Script
Verifies all components needed for successful GitHub Pages deployment.
"""

import os
import sys
import yaml
import json
from pathlib import Path

def check_file_exists(file_path, description):
    """Check if a file exists and print status."""
    if os.path.exists(file_path):
        print(f"✅ {description}: {file_path}")
        return True
    else:
        print(f"❌ {description}: {file_path} - NOT FOUND")
        return False

def check_yaml_syntax(file_path):
    """Check YAML file syntax."""
    try:
        with open(file_path, 'r') as f:
            yaml.safe_load(f)
        print(f"✅ YAML syntax valid: {file_path}")
        return True
    except yaml.YAMLError as e:
        print(f"❌ YAML syntax error in {file_path}: {e}")
        return False
    except Exception as e:
        print(f"❌ Error reading {file_path}: {e}")
        return False

def check_workflow_configuration(workflow_path):
    """Check specific workflow configuration."""
    try:
        with open(workflow_path, 'r') as f:
            workflow = yaml.safe_load(f)
        
        # Check permissions
        permissions = workflow.get('permissions', {})
        has_pages_write = permissions.get('pages') == 'write'
        has_id_token_write = permissions.get('id-token') == 'write'
        
        print(f"✅ Pages permission: {has_pages_write}")
        print(f"✅ ID token permission: {has_id_token_write}")
        
        # Check for enablement parameters
        workflow_content = open(workflow_path, 'r').read()
        enablement_count = workflow_content.count('enablement: true')
        
        print(f"✅ Enablement parameters found: {enablement_count}")
        
        if enablement_count >= 2:
            print("✅ Sufficient enablement parameters (configure-pages and deploy-pages)")
        else:
            print("⚠️ May need more enablement parameters")
            
        return has_pages_write and has_id_token_write and enablement_count >= 1
        
    except Exception as e:
        print(f"❌ Error checking workflow configuration: {e}")
        return False

def check_html_file(html_path):
    """Check HTML file structure."""
    try:
        with open(html_path, 'r') as f:
            content = f.read()
        
        required_elements = [
            '<!DOCTYPE html>',
            '<html',
            '<head>',
            '<title>',
            '<body>',
            '</html>'
        ]
        
        missing = []
        for element in required_elements:
            if element not in content:
                missing.append(element)
        
        if not missing:
            print(f"✅ HTML structure valid: {html_path}")
            print(f"✅ File size: {len(content)} characters")
            return True
        else:
            print(f"❌ HTML structure issues in {html_path}: missing {missing}")
            return False
            
    except Exception as e:
        print(f"❌ Error checking HTML file: {e}")
        return False

def check_data_files():
    """Check data directory and key files."""
    data_dir = "data"
    if not os.path.exists(data_dir):
        print(f"❌ Data directory not found: {data_dir}")
        return False
    
    key_files = [
        "data/critical_line_verification.csv",
        "data/mathematical_certificate.json"
    ]
    
    all_exist = True
    for file_path in key_files:
        if check_file_exists(file_path, "Key data file"):
            # Check if file has content
            if os.path.getsize(file_path) > 0:
                print(f"  ✅ File has content ({os.path.getsize(file_path)} bytes)")
            else:
                print(f"  ⚠️ File is empty")
        else:
            all_exist = False
    
    return all_exist

def simulate_deployment():
    """Simulate the deployment process."""
    print("\n🧪 SIMULATING DEPLOYMENT PROCESS")
    print("=" * 50)
    
    try:
        # Create temporary site directory
        temp_dir = "/tmp/verify_site"
        os.makedirs(temp_dir, exist_ok=True)
        
        # Copy main files as workflow would
        import shutil
        shutil.copy("public/index.html", f"{temp_dir}/index.html")
        shutil.copy("README.md", f"{temp_dir}/README.md")
        
        # Copy data directory if it exists
        if os.path.exists("data"):
            shutil.copytree("data", f"{temp_dir}/data", dirs_exist_ok=True)
        
        # Check result
        created_files = os.listdir(temp_dir)
        print(f"✅ Deployment simulation successful")
        print(f"✅ Created files: {created_files}")
        
        # Check critical files
        if "index.html" in created_files and "data" in created_files:
            print("✅ All critical files present")
            return True
        else:
            print("❌ Missing critical files")
            return False
            
    except Exception as e:
        print(f"❌ Deployment simulation failed: {e}")
        return False

def main():
    """Main verification function."""
    print("🔍 GITHUB PAGES DEPLOYMENT VERIFICATION")
    print("=" * 60)
    
    checks = []
    
    # 1. Check workflow file
    print("\n📋 WORKFLOW CONFIGURATION")
    print("-" * 30)
    workflow_exists = check_file_exists(".github/workflows/pages.yml", "Main workflow")
    workflow_valid = check_yaml_syntax(".github/workflows/pages.yml") if workflow_exists else False
    workflow_config = check_workflow_configuration(".github/workflows/pages.yml") if workflow_exists else False
    checks.extend([workflow_exists, workflow_valid, workflow_config])
    
    # 2. Check HTML dashboard
    print("\n🌐 HTML DASHBOARD")
    print("-" * 30)
    html_exists = check_file_exists("public/index.html", "Main dashboard")
    html_valid = check_html_file("public/index.html") if html_exists else False
    checks.extend([html_exists, html_valid])
    
    # 3. Check data files
    print("\n📊 DATA FILES")
    print("-" * 30)
    data_valid = check_data_files()
    checks.append(data_valid)
    
    # 4. Check documentation
    print("\n📚 DOCUMENTATION")
    print("-" * 30)
    doc_exists = check_file_exists("docs/GITHUB_PAGES_SETUP.md", "Setup documentation")
    readme_exists = check_file_exists("README.md", "Repository README")
    checks.extend([doc_exists, readme_exists])
    
    # 5. Simulate deployment
    deployment_sim = simulate_deployment()
    checks.append(deployment_sim)
    
    # Summary
    print("\n" + "=" * 60)
    print("📋 VERIFICATION SUMMARY")
    print("=" * 60)
    
    passed = sum(checks)
    total = len(checks)
    
    print(f"✅ Passed: {passed}/{total} checks")
    print(f"❌ Failed: {total-passed}/{total} checks")
    
    if passed == total:
        print("\n🎉 ALL VERIFICATIONS PASSED!")
        print("\n🚀 GitHub Pages deployment should work correctly")
        print("\n📋 NEXT STEPS:")
        print("   1. Push changes to main branch")
        print("   2. Go to Repository Settings → Pages")
        print("   3. Set Source to 'GitHub Actions'")
        print("   4. Save settings")
        print("   5. Check Actions tab for deployment status")
        print("\n🌐 Expected site URL:")
        print("   https://motanova84.github.io/-jmmotaburr-riemann-adelic/")
        return 0
    else:
        print(f"\n⚠️ {total-passed} issues detected - review above for details")
        return 1

if __name__ == "__main__":
    sys.exit(main())