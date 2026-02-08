"""
void_life_comparison.py - Classical vs Resource-Limited Conway side-by-side
Shows how finite resources create impossible states
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.colors import LinearSegmentedColormap

# ============================================================================
# FINITE KERNEL WITH SCALED INTEGERS
# ============================================================================

SCALE = 1000
HALF = SCALE // 2

class Fin:
    def __init__(self, n: int = 0):
        self.n = min(n, SCALE * 10)  # Higher cap for longer life
    
    def __add__(self, other):
        return Fin(min(self.n + other.n, SCALE * 10))
    
    def __sub__(self, other):
        return Fin(max(self.n - other.n, 0))
    
    def is_zero(self):
        return self.n == 0

# ============================================================================
# CLASSICAL CONWAY (for comparison)
# ============================================================================

class ClassicalConway:
    """Standard Conway's Life - no resources, two states only"""
    
    def __init__(self, size: int):
        self.size = size
        self.grid = np.zeros((size, size), dtype=int)
        self.generation = 0
    
    def seed_pattern(self, pattern):
        """Same initial pattern as resource-limited version"""
        center = self.size // 2
        np.random.seed(42)
        
        # Random soup in center
        for i in range(center-8, center+8):
            for j in range(center-8, center+8):
                if np.random.random() > 0.5:
                    self.grid[i][j] = 1
        
        # Some cells near edges
        for i in range(self.size):
            for j in range(self.size):
                dist = min(i, j, self.size-i-1, self.size-j-1)
                if dist <= 3 and np.random.random() > 0.7:
                    self.grid[i][j] = 1
    
    def step(self):
        """Classical Conway rules - no resource cost"""
        new_grid = np.zeros_like(self.grid)
        
        for i in range(self.size):
            for j in range(self.size):
                # Count neighbors
                neighbors = 0
                for di in [-1, 0, 1]:
                    for dj in [-1, 0, 1]:
                        if di == 0 and dj == 0:
                            continue
                        ni = (i + di) % self.size
                        nj = (j + dj) % self.size
                        neighbors += self.grid[ni][nj]
                
                # Apply rules
                if self.grid[i][j] == 1:
                    if neighbors in [2, 3]:
                        new_grid[i][j] = 1
                else:
                    if neighbors == 3:
                        new_grid[i][j] = 1
        
        self.grid = new_grid
        self.generation += 1

# ============================================================================
# RESOURCE-LIMITED CONWAY WITH FINITE RESOURCES
# ============================================================================

class ResourceLimitedConway:
    """Conway with finite resources - creates undecidable states"""
    
    def __init__(self, size: int):
        self.size = size
        self.generation = 0
        self.grid = []
        
        for i in range(size):
            row = []
            for j in range(size):
                # Budget gradient - edges exhaust first
                dist = min(i, j, size-i-1, size-j-1)
                if dist <= 3:
                    budget = Fin(100)  # Low budget at edges
                elif dist <= 8:
                    budget = Fin(500)  # Medium
                else:
                    budget = Fin(2000)  # High in center
                
                cell = {'state': 0, 'budget': budget, 'exhaustion_counter': 0}
                row.append(cell)
            self.grid.append(row)
    
    def seed_pattern(self, pattern):
        """Same pattern as classical"""
        center = self.size // 2
        np.random.seed(42)
        
        for i in range(center-8, center+8):
            for j in range(center-8, center+8):
                if np.random.random() > 0.5:
                    self.grid[i][j]['state'] = 1
        
        for i in range(self.size):
            for j in range(self.size):
                dist = min(i, j, self.size-i-1, self.size-j-1)
                if dist <= 3 and np.random.random() > 0.7:
                    self.grid[i][j]['state'] = 1
                    self.grid[i][j]['budget'] = Fin(80)  # Less budget at edges
    
    def step(self):
        """Resource-limited Conway - costs resources"""
        new_states = []
        
        for i in range(self.size):
            row = []
            for j in range(self.size):
                cell = self.grid[i][j]
                
                # Count neighbors
                alive_n = 0
                unknown_n = 0
                for di in [-1, 0, 1]:
                    for dj in [-1, 0, 1]:
                        if di == 0 and dj == 0:
                            continue
                        ni = (i + di) % self.size
                        nj = (j + dj) % self.size
                        neighbor_state = self.grid[ni][nj]['state']
                        if neighbor_state == 1:
                            alive_n += 1
                        elif neighbor_state == -1:  # Unknown/exhausted
                            unknown_n += 1
                
                # Compute next state
                if cell['budget'].is_zero():
                    # No budget - increment exhaustion counter
                    cell['exhaustion_counter'] += 1
                    if cell['exhaustion_counter'] > 5:
                        new_state = -1  # Become unknown
                    else:
                        new_state = cell['state']
                else:
                    # Spend one tick
                    cell['budget'] = cell['budget'] - Fin(1)
                    
                    if cell['state'] == -1:  # Unknown/exhausted
                        if unknown_n >= 2:
                            new_state = -1  # Stay unknown
                        elif alive_n >= 3 and cell['budget'].n > 100:
                            new_state = 1  # Recover to alive
                        else:
                            new_state = -1
                    else:
                        # Use scaled integer arithmetic
                        eff = alive_n * SCALE + unknown_n * HALF
                        
                        if cell['state'] == 1:  # Alive
                            if 2 * SCALE <= eff <= 3 * SCALE:
                                new_state = 1
                            elif eff > 4 * SCALE and unknown_n > 2:
                                cell['exhaustion_counter'] += 1
                                if cell['exhaustion_counter'] > 3:
                                    new_state = -1  # Become unknown
                                else:
                                    new_state = 1
                            else:
                                new_state = 0  # Die
                        else:  # Dead
                            if 2500 <= eff <= 3500:  # 2.5 to 3.5
                                new_state = 1  # Birth
                            elif unknown_n >= 4:
                                cell['exhaustion_counter'] += 1
                                if cell['exhaustion_counter'] > 2:
                                    new_state = -1  # Become unknown
                                else:
                                    new_state = 0
                            else:
                                new_state = 0
                
                row.append(new_state)
            new_states.append(row)
        
        # Apply new states
        for i in range(self.size):
            for j in range(self.size):
                self.grid[i][j]['state'] = new_states[i][j]
        
        self.generation += 1

# ============================================================================
# SIDE-BY-SIDE COMPARISON
# ============================================================================

def run_comparison():
    """Run classical and resource-limited Conway side by side"""
    
    size = 60
    classical = ClassicalConway(size)
    resource_limited = ResourceLimitedConway(size)
    
    # Same initial conditions
    classical.seed_pattern('test')
    resource_limited.seed_pattern('test')
    
    # Setup visualization
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    fig.suptitle('Classical vs Resource-Limited Conway: Finite Resources Create New States')
    
    # Colormaps
    classical_cmap = 'binary'
    exhausted_cmap = LinearSegmentedColormap.from_list('exhausted', ['black', 'gold', 'white'])
    
    # Stats tracking
    history = {
        'classical_alive': [],
        'limited_alive': [],
        'unknown_count': [],
        'total_budget': []
    }
    
    def update(frame):
        # Step both simulations
        classical.step()
        resource_limited.step()
        
        # Classical visualization
        axes[0, 0].clear()
        axes[0, 0].imshow(classical.grid, cmap=classical_cmap, vmin=0, vmax=1)
        axes[0, 0].set_title(f'Classical Conway - Gen {classical.generation}')
        axes[0, 0].set_xticks([])
        axes[0, 0].set_yticks([])
        
        # Resource-limited visualization
        limited_matrix = np.zeros((size, size))
        budget_matrix = np.zeros((size, size))
        
        alive_limited = 0
        unknown_count = 0
        total_budget = 0
        
        for i in range(size):
            for j in range(size):
                cell = resource_limited.grid[i][j]
                state = cell['state']
                
                if state == 1:
                    limited_matrix[i][j] = 1.0
                    alive_limited += 1
                elif state == 0:
                    limited_matrix[i][j] = 0.0
                else:  # Unknown/exhausted state
                    limited_matrix[i][j] = 0.5
                    unknown_count += 1
                
                budget_matrix[i][j] = cell['budget'].n
                total_budget += cell['budget'].n
        
        axes[0, 1].clear()
        axes[0, 1].imshow(limited_matrix, cmap=exhausted_cmap, vmin=-1, vmax=1)
        axes[0, 1].set_title(f'Resource-Limited Conway - Gen {resource_limited.generation}')
        axes[0, 1].set_xticks([])
        axes[0, 1].set_yticks([])
        
        # Budget heatmap
        axes[0, 2].clear()
        im = axes[0, 2].imshow(budget_matrix, cmap='hot', vmin=0, vmax=2000)
        axes[0, 2].set_title('Remaining Computational Budget')
        axes[0, 2].set_xticks([])
        axes[0, 2].set_yticks([])
        
        # Classical stats
        classical_alive = np.sum(classical.grid)
        history['classical_alive'].append(classical_alive)
        history['limited_alive'].append(alive_limited)
        history['unknown_count'].append(unknown_count)
        history['total_budget'].append(total_budget)
        
        # Population dynamics
        axes[1, 0].clear()
        x = list(range(len(history['classical_alive'])))
        axes[1, 0].plot(x, history['classical_alive'], 'b-', label='Classical Alive')
        axes[1, 0].plot(x, history['limited_alive'], 'g-', label='Limited Alive')
        axes[1, 0].plot(x, history['unknown_count'], 'gold', label='Unknown/Exhausted', linewidth=2)
        axes[1, 0].set_xlabel('Generation')
        axes[1, 0].set_ylabel('Cell Count')
        axes[1, 0].set_title('Population Dynamics')
        axes[1, 0].legend()
        axes[1, 0].grid(True, alpha=0.3)
        
        # Resource depletion
        axes[1, 1].clear()
        axes[1, 1].plot(x, history['total_budget'], 'r-', linewidth=2)
        axes[1, 1].set_xlabel('Generation')
        axes[1, 1].set_ylabel('Total Budget')
        axes[1, 1].set_title('Computational Cost of Decisions')
        axes[1, 1].grid(True, alpha=0.3)
        
        # Key differences text
        axes[1, 2].clear()
        axes[1, 2].axis('off')
        
        differences = f"""KEY DIFFERENCES AT GEN {resource_limited.generation}:
        
Classical Conway:
- Two states only (alive/dead)
- Computation is free
- {classical_alive:.0f} living cells
- Patterns cycle forever
- No resource concept

Resource-Limited Conway:
- THREE states (alive/dead/unknown)
- Every decision costs resources
- {alive_limited:.0f} alive, {unknown_count:.0f} unknown
- Budget remaining: {total_budget:.0f}
- Unknown zones emerge at boundaries

IMPOSSIBLE IN CLASSICAL:
- Unknown state at edges (gold)
- Resource exhaustion zones
- Three-valued logic (T/F/U)
- Computational reality
        """
        
        axes[1, 2].text(0.1, 0.5, differences, fontsize=10, 
                       verticalalignment='center', family='monospace')
        
        return []
    
    anim = FuncAnimation(fig, update, frames=300, interval=100)
    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    print("=" * 70)
    print("CLASSICAL vs RESOURCE-LIMITED CONWAY")
    print("Finite resources create states impossible in classical mathematics")
    print("=" * 70)
    
    run_comparison()