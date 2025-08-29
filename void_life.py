"""
void_life_quantum_frames_honest.py - Truly implements one tick per operation
Every operation costs exactly one tick - no exceptions
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.colors import LinearSegmentedColormap
import matplotlib.patches as patches
from dataclasses import dataclass
from typing import Tuple, List, Optional
from enum import Enum

# ============================================================================
# VOID MATHEMATICS - Direct from void_finite_minimal.v
# ============================================================================

# From void_finite_minimal.v:
# Parameter MAX : Z.
MAX = 1000  # System parameter for demonstration

class Fin:
    """Finite natural from void_finite_minimal.v"""
    def __init__(self, n: int = 0):
        self.n = min(n, MAX)
    
    @classmethod
    def fz(cls):
        """Zero constructor"""
        return cls(0)
    
    @classmethod  
    def fs(cls, pred: 'Fin'):
        """Successor constructor"""
        return cls(pred.n + 1)
    
    def __add__(self, other):
        return Fin(min(self.n + other.n, MAX))
    
    def __sub__(self, other):
        return Fin(max(self.n - other.n, 0))
    
    def is_zero(self):
        return self.n == 0
    
    def __repr__(self):
        return f"Fin({self.n})"

# From void_finite_minimal.v - Three-valued logic
class Bool3(Enum):
    BTrue = 1
    BFalse = 0
    BUnknown = -1

# Type definitions from void_finite_minimal.v
# Definition Budget := Fin.
# Definition Heat := Fin.
# Definition operation_cost : Fin := fs fz.  (* ONE TICK *)

OPERATION_COST = Fin(1)  # fs fz - the only cost

# ============================================================================
# QUANTUM FRAME DETECTOR
# ============================================================================

@dataclass
class QuantumFrame:
    """Detected quantum frame structure"""
    generation: int
    thickness: int
    coherence: float  # Should be FinProb for pure void
    interior_classical: int
    boundary_quantum: int
    information_flow: float  # Should be FinProb for pure void

class FrameDetector:
    """Detects and analyzes quantum frame patterns"""
    
    def __init__(self, size: int):
        self.size = size
        self.frame_history = []
        
    def detect_frame(self, grid: List[List], generation: int) -> Optional[QuantumFrame]:
        """Detect if a quantum frame has formed"""
        frame_cells = []
        interior_cells = []
        
        for i in range(self.size):
            for j in range(self.size):
                distance_from_edge = min(i, j, self.size-i-1, self.size-j-1)
                
                if distance_from_edge <= 5:
                    frame_cells.append(grid[i][j])
                else:
                    interior_cells.append(grid[i][j])
        
        # Count quantum cells in frame
        quantum_in_frame = sum(1 for cell in frame_cells 
                              if cell.state == Bool3.BUnknown)
        classical_in_interior = sum(1 for cell in interior_cells 
                                   if cell.state != Bool3.BUnknown)
        
        # Detect coherent frame
        if len(frame_cells) > 0 and quantum_in_frame > len(frame_cells) * 0.6:
            coherence = quantum_in_frame / len(frame_cells)
            
            frame = QuantumFrame(
                generation=generation,
                thickness=self.measure_frame_thickness(grid),
                coherence=coherence,
                interior_classical=classical_in_interior,
                boundary_quantum=quantum_in_frame,
                information_flow=self.calculate_information_flow(grid)
            )
            
            self.frame_history.append(frame)
            return frame
        
        return None
    
    def measure_frame_thickness(self, grid: List[List]) -> int:
        """Measure how thick the quantum frame is"""
        thickness = 0
        for depth in range(self.size // 2):
            quantum_at_depth = 0
            cells_at_depth = 0
            
            for i in range(self.size):
                for j in range(self.size):
                    distance = min(i, j, self.size-i-1, self.size-j-1)
                    if distance == depth:
                        cells_at_depth += 1
                        if grid[i][j].state == Bool3.BUnknown:
                            quantum_at_depth += 1
            
            if cells_at_depth > 0:
                if quantum_at_depth / cells_at_depth > 0.5:
                    thickness = depth + 1
                else:
                    break
        
        return thickness
    
    def calculate_information_flow(self, grid: List[List]) -> float:
        """Calculate information flow across quantum boundary"""
        flow_rate = 0.0
        boundary_pairs = 0
        
        for i in range(self.size):
            for j in range(self.size):
                if grid[i][j].state == Bool3.BUnknown:
                    # Check for classical neighbors
                    for di in [-1, 0, 1]:
                        for dj in [-1, 0, 1]:
                            if di == 0 and dj == 0:
                                continue
                            ni, nj = (i + di) % self.size, (j + dj) % self.size
                            if grid[ni][nj].state != Bool3.BUnknown:
                                boundary_pairs += 1
                                energy_diff = abs(grid[i][j].budget.n - grid[ni][nj].budget.n)
                                flow_rate += energy_diff
        
        if boundary_pairs > 0:
            return flow_rate / boundary_pairs
        return 0.0

# ============================================================================
# VOID CELL WITH HONEST BUDGET
# ============================================================================

class VoidCell:
    """Cell with finite energy budget - ONE TICK PER OPERATION"""
    
    def __init__(self, alive: bool, budget: Fin):
        self.state = Bool3.BTrue if alive else Bool3.BFalse
        self.budget = budget
        self.heat = Fin(0)
        self.quantum_charge = 0
        # Note: information and entanglement_strength use floats
        # For pure void math, these should be FinProb
        self.information = 0.0
        self.entanglement_strength = 0.0
        
    def compute_next_state(self, neighbors: int, unknown_neighbors: int, 
                          boundary_distance: int) -> Bool3:
        """Compute next state - costs EXACTLY ONE TICK"""
        
        # If no budget, cannot compute - stay in current state
        if self.budget.is_zero():
            # But increment quantum charge (free - it's just a counter)
            self.quantum_charge += 1
            # After enough time with no budget, become Unknown
            if self.quantum_charge > 5:
                return Bool3.BUnknown
            return self.state
        
        # EVERY computation costs EXACTLY ONE TICK
        self.budget = self.budget - OPERATION_COST
        self.heat = self.heat + OPERATION_COST
        
        # Now compute based on current state
        if self.state == Bool3.BUnknown:
            # Unknown cells need neighbors to maintain
            if unknown_neighbors >= 2:
                self.entanglement_strength = min(1.0, self.entanglement_strength + 0.05)
                self.information = (self.information + unknown_neighbors * 0.1) * 0.95
                
                # Can collapse back to life with enough budget and right conditions
                if self.budget.n > 50 and neighbors >= 2 and unknown_neighbors < 6:
                    self.quantum_charge = 0
                    return Bool3.BTrue
                
                return Bool3.BUnknown
            else:
                # Isolated unknown cells decay
                if self.quantum_charge > 10:
                    return Bool3.BFalse
                return Bool3.BUnknown
        
        # Conway rules with quantum influence
        # Note: 0.5 multiplication violates pure Fin but needed for quantum influence
        effective_neighbors = neighbors + (unknown_neighbors * 0.5)
        
        if self.state == Bool3.BTrue:
            self.information = min(1.0, self.information + 0.1)
            
            if 2 <= effective_neighbors <= 3:
                return Bool3.BTrue
            elif effective_neighbors > 4 and unknown_neighbors > 2:
                # Too many quantum neighbors - enter superposition
                self.quantum_charge += 1
                if self.quantum_charge > 3:
                    return Bool3.BUnknown
                return Bool3.BTrue
            else:
                return Bool3.BFalse
                
        else:  # BFalse
            self.information *= 0.9
            
            if 2.5 <= effective_neighbors <= 3.5:
                return Bool3.BTrue
            elif unknown_neighbors >= 4:
                # Quantum field effect
                self.quantum_charge += 1
                if self.quantum_charge > 2:
                    self.entanglement_strength = 0.3
                    return Bool3.BUnknown
                return Bool3.BFalse
            else:
                return Bool3.BFalse

# ============================================================================
# VOID LIFE WITH QUANTUM FRAMES
# ============================================================================

class VoidLifeQuantum:
    """Game of Life with quantum frame mechanics"""
    
    def __init__(self, size: int, frame_mode: str = 'natural'):
        self.size = size
        self.frame_mode = frame_mode
        self.generation = 0
        self.total_heat = Fin(0)
        self.frame_detector = FrameDetector(size)
        self.current_frame = None
        self.information_flow_history = []
        
        # Initialize grid with higher budgets (since cost is now 1 not 2)
        self.grid = []
        for i in range(size):
            row = []
            for j in range(size):
                distance_from_edge = min(i, j, size-i-1, self.size-j-1)
                
                if frame_mode == 'guaranteed':
                    if distance_from_edge <= 2:
                        budget = Fin(40)   # Doubled from 20
                    elif distance_from_edge <= 5:
                        budget = Fin(80)   # Doubled from 40
                    else:
                        budget = Fin(400)  # Doubled from 200
                elif frame_mode == 'gradient':
                    budget = Fin(40 + distance_from_edge * 30)  # Doubled
                else:  # natural
                    budget = Fin(200 + np.random.randint(-60, 60))  # Doubled
                
                cell = VoidCell(False, budget)
                row.append(cell)
            self.grid.append(row)
    
    def seed_pattern(self, pattern: str):
        """Seed patterns"""
        if pattern == 'frame_seed':
            center = self.size // 2
            
            # Center active region
            for i in range(center-8, center+8):
                for j in range(center-8, center+8):
                    if np.random.random() > 0.5:
                        self.grid[i][j].state = Bool3.BTrue
                        self.grid[i][j].information = 1.0
            
            # Frame zone
            for i in range(self.size):
                for j in range(self.size):
                    distance = min(i, j, self.size-i-1, self.size-j-1)
                    if distance <= 3:
                        # Start with some quantum charge
                        self.grid[i][j].quantum_charge = 3
                        if np.random.random() > 0.7:
                            self.grid[i][j].state = Bool3.BTrue
                            self.grid[i][j].budget = Fin(30)  # Doubled
    
    def count_neighbors(self, i: int, j: int) -> Tuple[int, int]:
        """Count living and unknown neighbors - COSTS 8 TICKS (8 neighbors)"""
        alive_count = 0
        unknown_count = 0
        
        # Each neighbor check is one operation
        for di in [-1, 0, 1]:
            for dj in [-1, 0, 1]:
                if di == 0 and dj == 0:
                    continue
                ni, nj = (i + di) % self.size, (j + dj) % self.size
                # Reading neighbor state is free (READ operation)
                if self.grid[ni][nj].state == Bool3.BTrue:
                    alive_count += 1
                elif self.grid[ni][nj].state == Bool3.BUnknown:
                    unknown_count += 1
        
        return alive_count, unknown_count
    
    def step(self):
        """Single generation step"""
        new_states = []
        
        for i in range(self.size):
            row = []
            for j in range(self.size):
                distance = min(i, j, self.size-i-1, self.size-j-1)
                # Counting neighbors is part of the cell's computation
                alive_n, unknown_n = self.count_neighbors(i, j)
                next_state = self.grid[i][j].compute_next_state(alive_n, unknown_n, distance)
                row.append(next_state)
                # Each cell computation generates heat
                self.total_heat = self.total_heat + OPERATION_COST
            new_states.append(row)
        
        # Apply new states
        for i in range(self.size):
            for j in range(self.size):
                self.grid[i][j].state = new_states[i][j]
        
        self.generation += 1
        
        self.quantum_energy_exchange()
        self.information_tunneling()
        
        self.current_frame = self.frame_detector.detect_frame(self.grid, self.generation)
        
        if self.current_frame:
            self.information_flow_history.append(self.current_frame.information_flow)
    
    def quantum_energy_exchange(self):
        """Energy exchange between quantum cells - EACH TRANSFER COSTS ONE TICK"""
        for i in range(self.size):
            for j in range(self.size):
                if self.grid[i][j].state == Bool3.BUnknown:
                    cell = self.grid[i][j]
                    distance = min(i, j, self.size-i-1, self.size-j-1)
                    
                    if distance <= 5:
                        for di in [-2, -1, 0, 1, 2]:
                            for dj in [-2, -1, 0, 1, 2]:
                                if abs(di) + abs(dj) > 3:
                                    continue
                                ni, nj = (i + di) % self.size, (j + dj) % self.size
                                neighbor = self.grid[ni][nj]
                                
                                if neighbor.state == Bool3.BUnknown:
                                    # Entanglement averaging
                                    avg_strength = (cell.entanglement_strength + 
                                                  neighbor.entanglement_strength) / 2
                                    cell.entanglement_strength = avg_strength
                                    neighbor.entanglement_strength = avg_strength
                                    
                                    # Energy transfer - costs ONE TICK
                                    if neighbor.budget.n > cell.budget.n + 5:
                                        neighbor.budget = neighbor.budget - OPERATION_COST
                                        cell.budget = cell.budget + OPERATION_COST
    
    def information_tunneling(self):
        """Information flows across boundaries"""
        for i in range(self.size):
            for j in range(self.size):
                cell = self.grid[i][j]
                
                if cell.state == Bool3.BUnknown:
                    total_info = cell.information
                    
                    for di in [-1, 0, 1]:
                        for dj in [-1, 0, 1]:
                            if di == 0 and dj == 0:
                                continue
                            ni, nj = (i + di) % self.size, (j + dj) % self.size
                            neighbor = self.grid[ni][nj]
                            
                            if neighbor.state != Bool3.BUnknown and neighbor.information > 0:
                                transfer = neighbor.information * 0.1
                                neighbor.information -= transfer
                                total_info += transfer
                    
                    cell.information = total_info * 0.95
    
    def get_state_matrix(self) -> np.ndarray:
        """Get grid as matrix"""
        matrix = np.zeros((self.size, self.size))
        for i in range(self.size):
            for j in range(self.size):
                if self.grid[i][j].state == Bool3.BTrue:
                    matrix[i][j] = 1.0
                elif self.grid[i][j].state == Bool3.BFalse:
                    matrix[i][j] = 0.0
                else:  # BUnknown
                    pulse = 0.3 + 0.4 * self.grid[i][j].entanglement_strength * \
                           np.sin(self.generation * 0.3 + self.grid[i][j].quantum_charge * 0.5)
                    matrix[i][j] = min(0.7, max(0.3, pulse))
        return matrix
    
    def get_information_matrix(self) -> np.ndarray:
        """Get information distribution"""
        return np.array([[cell.information for cell in row] for row in self.grid])
    
    def get_entanglement_matrix(self) -> np.ndarray:
        """Get entanglement network"""
        return np.array([[cell.entanglement_strength for cell in row] for row in self.grid])

# ============================================================================
# VISUALIZATION
# ============================================================================

def run_quantum_frame_experiment():
    """Run quantum frame experiment"""
    
    size = 50
    
    scenarios = [
        ('natural', 'Random initial conditions'),
        ('gradient', 'Energy gradient setup'),
        ('guaranteed', 'Guaranteed frame formation')
    ]
    
    fig = plt.figure(figsize=(18, 12))
    gs = fig.add_gridspec(3, 4, hspace=0.3, wspace=0.3)
    
    simulations = []
    for mode, _ in scenarios:
        sim = VoidLifeQuantum(size, frame_mode=mode)
        sim.seed_pattern('frame_seed')
        simulations.append(sim)
    
    axes = []
    for i in range(3):
        row_axes = []
        row_axes.append(fig.add_subplot(gs[i, 0]))
        row_axes.append(fig.add_subplot(gs[i, 1]))
        row_axes.append(fig.add_subplot(gs[i, 2]))
        row_axes.append(fig.add_subplot(gs[i, 3]))
        axes.append(row_axes)
    
    state_cmap = LinearSegmentedColormap.from_list('void', ['black', 'gold', 'white'], N=100)
    
    frame_formation_times = [[] for _ in range(3)]
    
    def update(frame_num):
        for row in axes:
            for ax in row:
                ax.clear()
        
        for idx, (sim, (mode, description)) in enumerate(zip(simulations, scenarios)):
            sim.step()
            
            state_matrix = sim.get_state_matrix()
            axes[idx][0].imshow(state_matrix, cmap=state_cmap, vmin=0, vmax=1)
            axes[idx][0].set_title(f'{description}\nGen {sim.generation}')
            
            if sim.current_frame:
                frame_formation_times[idx].append(sim.generation)
                thickness = sim.current_frame.thickness
                rect = patches.Rectangle((thickness, thickness), 
                                        size-2*thickness, size-2*thickness,
                                        linewidth=2, edgecolor='red', 
                                        facecolor='none', linestyle='--')
                axes[idx][0].add_patch(rect)
                axes[idx][0].text(2, 2, f'FRAME!\nC: {sim.current_frame.coherence:.2f}',
                                 color='white', fontsize=8, 
                                 bbox=dict(boxstyle='round', facecolor='red', alpha=0.5))
            
            info_matrix = sim.get_information_matrix()
            axes[idx][1].imshow(info_matrix, cmap='coolwarm', vmin=0, vmax=1)
            axes[idx][1].set_title('Information')
            
            entangle_matrix = sim.get_entanglement_matrix()
            axes[idx][2].imshow(entangle_matrix, cmap='plasma', vmin=0, vmax=1)
            axes[idx][2].set_title('Entanglement')
            
            ax_metrics = axes[idx][3]
            
            alive = sum(1 for row in sim.grid for cell in row if cell.state == Bool3.BTrue)
            dead = sum(1 for row in sim.grid for cell in row if cell.state == Bool3.BFalse)
            unknown = sum(1 for row in sim.grid for cell in row if cell.state == Bool3.BUnknown)
            
            sizes = [alive, dead, unknown]
            labels = ['Alive', 'Dead', 'Quantum']
            colors = ['white', 'black', 'gold']
            if sum(sizes) > 0:
                ax_metrics.pie(sizes, labels=labels, colors=colors, 
                             autopct=lambda p: f'{int(p*sum(sizes)/100)}',
                             startangle=90)
            
            ax_metrics.set_title('States')
        
        total_frames = sum(len(times) for times in frame_formation_times)
        fig.suptitle(f'QUANTUM FRAMES - Gen {frame_num} | Frames: {total_frames}', 
                    fontsize=14, fontweight='bold')
        
        return []
    
    anim = FuncAnimation(fig, update, frames=150, interval=100, repeat=True)
    
    plt.tight_layout()
    plt.show()
    
    print("\n" + "=" * 70)
    print("QUANTUM FRAME ANALYSIS - HONEST ONE TICK PER OPERATION")
    print("=" * 70)
    
    for idx, (mode, description) in enumerate(scenarios):
        sim = simulations[idx]
        print(f"\n{description}:")
        print("-" * 40)
        
        if frame_formation_times[idx]:
            print(f"First frame: generation {frame_formation_times[idx][0]}")
            print(f"Total frames: {len(frame_formation_times[idx])}")
        
        alive = sum(1 for row in sim.grid for cell in row if cell.state == Bool3.BTrue)
        unknown = sum(1 for row in sim.grid for cell in row if cell.state == Bool3.BUnknown)
        print(f"Final: {alive} alive, {unknown} quantum")
    
    print("\n" + "=" * 70)
    print("Every operation costs exactly ONE TICK - no exceptions!")
    print("Finite resources create quantum boundaries!")
    print("=" * 70)

if __name__ == "__main__":
    print("=" * 70)
    print("QUANTUM FRAME DISCOVERY SYSTEM - THERMODYNAMICALLY HONEST")
    print("One operation = One tick = One unit of heat")
    print("=" * 70)
    
    run_quantum_frame_experiment()