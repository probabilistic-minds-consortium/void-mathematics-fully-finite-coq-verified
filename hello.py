from dataclasses import dataclass
from typing import Optional, Tuple

# 1. System Constants (Axioms)
MAX_INT = 100  # Nasza skończoność
OP_COST = 1    # Koszt każdej operacji (μ-tick)

# 2. Core Types
@dataclass
class VoidState:
    value: int
    budget: int
    heat: int

    def __repr__(self):
        return f"[Val: {self.value} | B: {self.budget} | H: {self.heat}]"

# 3. Safe Primitive (Bounded Integer)
def to_fin(n: int) -> int:
    """Zapewnia, że liczba nie ucieka w nieskończoność."""
    return min(n, MAX_INT)

# 4. The VOID Operation (Addition)
def void_add(n: int, m: int, budget: int) -> VoidState:
    """
    Dodawanie w systemie VOID.
    Każdy krok (każda jednostka dodawana) kosztuje 1 tik budżetu.
    """
    # Base Case: Jeśli m to 0, wynik to n, koszt 0 (READ operation)
    if m == 0:
        return VoidState(n, budget, 0)
    
    # Check Budget (Safety Fuse)
    if budget <= 0:
        # EXHAUSTION: Nie stać nas na policzenie wyniku.
        # Zwracamy to, co mamy (n), budżet 0, ciepło 0.
        # To jest odpowiednik Twojego "U" lub "Degraded Result".
        return VoidState(n, 0, 0)  

    # Recursive Step Simulation (kosztuje 1 tik)
    # m -> m-1, n -> n+1
    # Recursion: void_add(n+1, m-1, budget-1)
    
    # Symulujemy rekurencję w pętli dla czytelności, 
    # ale zachowujemy logikę kosztu za każdy krok.
    current_n = n
    current_m = m
    current_budget = budget
    total_heat = 0
    
    while current_m > 0 and current_budget > 0:
        current_m -= 1
        current_n = to_fin(current_n + 1)
        
        # Płacimy za operację
        current_budget -= OP_COST
        total_heat += OP_COST
        
    # Final Check: Czy skończyliśmy, czy zabrakło prądu?
    if current_m > 0:
        # Zabrakło budżetu w trakcie! Zwracamy wynik częściowy.
        print("!!! SYSTEM HALTED: OUT OF BUDGET !!!")
        return VoidState(current_n, 0, total_heat)
    
    return VoidState(current_n, current_budget, total_heat)

# --- DEMO SCENARIO ---

print("--- SCENARIUSZ 1: Bogaty Obserwator ---")
# Mamy dużo budżetu (50), dodajemy 5 + 3
result_rich = void_add(5, 3, budget=50)
print(f"Wynik: {result_rich}")
# Oczekiwane: Val: 8, B: 47 (zużyto 3), H: 3

print("\n--- SCENARIUSZ 2: Biedny Obserwator (Exhaustion) ---")
# Mamy mało budżetu (2), dodajemy 5 + 5
# System powinien "paść" w połowie liczenia.
result_poor = void_add(5, 5, budget=2)
print(f"Wynik: {result_poor}")
# Oczekiwane: Val: 7 (nie 10!), B: 0, H: 2. System "zgasł".