#!/bin/bash
echo "Setting up Mathlib for Lean 4..."
cd ~/lean_workspace

# Check if lakefile exists
if [ ! -f lakefile.lean ] && [ ! -f lakefile.toml ]; then
  lake init aci_system
fi

# Add Mathlib dependency
cat > lakefile.toml << 'LAKE'
name = "aci_system"
version = "0.1.0"
defaultTargets = ["AciSystem"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "master"

[[lean_lib]]
name = "AciSystem"
LAKE

# Download Mathlib
lake update
echo "Mathlib update complete"
lake build Mathlib
echo "Mathlib build complete"
