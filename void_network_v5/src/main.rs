//! VOID Neural Network v0.5 - AUDITED
//! 
//! FIXES FROM GPT-5.2 AUDIT:
//! - Heat now tracks ALL budget spends (including ge/gt comparisons)
//! - Entropy weight uses saturating_mul to prevent overflow
//! - search_memory_bank returns exhausted flag; Match during exhaustion → Exhausted
//! - patterns_checked is now accurate
//!
//! ONTOLOGICAL AUDIT v3:
//! - NO IEEE 754 floats anywhere in logic
//! - Decimal notation ("0.625") parsed directly to Ratio(625, 1000)
//! - Cross-multiplication comparison (no division)
//! - saturating_add/mul for all counters (no overflow wrap)
//! - Heat = accumulated cost, now properly enforced
//!
//! Philosophy:
//! - Every operation costs budget AND generates heat
//! - When budget = 0, stop and say "I don't know" (or Exhausted if partial)
//! - Pattern matching, not matrix multiplication
//! - Network grows by accretion (coral architecture)

use std::fs::File;
use std::io::BufReader;

// ============================================
// CORE TYPES - STRICTLY FINITE
// ============================================

/// Budget - the heartbeat of VOID. When it hits 0, observation stops.
#[derive(Debug, Clone, Copy)]
pub struct Budget(u32);

impl Budget {
    pub fn new(initial: u32) -> Self {
        Budget(initial)
    }
    
    /// Spend budget. Returns None if insufficient.
    /// IMPORTANT: Caller must also add heat!
    pub fn spend(&mut self, cost: u32) -> Option<u32> {
        if self.0 >= cost {
            self.0 -= cost;
            Some(self.0)
        } else {
            None
        }
    }
    
    pub fn remaining(&self) -> u32 {
        self.0
    }
    
    pub fn is_exhausted(&self) -> bool {
        self.0 == 0
    }
}

/// Heat - accumulated cost, irreversible trace
/// INVARIANT: Every budget.spend(n) must be accompanied by heat.add(n)
#[derive(Debug, Clone, Copy, Default)]
pub struct Heat(u32);

impl Heat {
    pub fn add(&mut self, amount: u32) {
        self.0 = self.0.saturating_add(amount);
    }
    
    pub fn total(&self) -> u32 {
        self.0
    }
}

/// ResourceContext bundles Budget and Heat together
/// This ensures every spend is tracked as heat
pub struct Resources {
    pub budget: Budget,
    pub heat: Heat,
}

impl Resources {
    pub fn new(initial_budget: u32) -> Self {
        Resources {
            budget: Budget::new(initial_budget),
            heat: Heat::default(),
        }
    }
    
    /// Spend budget AND record heat atomically
    /// This is the ONLY way to spend in v0.5
    pub fn spend(&mut self, cost: u32) -> Option<u32> {
        let result = self.budget.spend(cost)?;
        self.heat.add(cost);  // ALWAYS track heat
        Some(result)
    }
    
    pub fn is_exhausted(&self) -> bool {
        self.budget.is_exhausted()
    }
    
    pub fn remaining(&self) -> u32 {
        self.budget.remaining()
    }
    
    pub fn heat_total(&self) -> u32 {
        self.heat.total()
    }
}

// ============================================
// RATIO - TRUE FINITE ARITHMETIC
// ============================================

/// Ratio represents certainty in VOID.
/// 
/// KEY INSIGHT: Decimal notation is NOT floating point!
/// "0.625" is just shorthand for 625/1000.
/// The heresy is IEEE 754, not the decimal point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ratio {
    pub n: u32,  // numerator
    pub d: u32,  // denominator
}

impl Ratio {
    pub fn new(n: u32, d: u32) -> Self {
        if d == 0 { 
            Ratio { n: 0, d: 1 } 
        } else { 
            Ratio { n, d } 
        }
    }
    
    pub fn zero() -> Self { 
        Ratio { n: 0, d: 1 } 
    }
    
    /// Returns true if this ratio represents an undefined/empty comparison
    pub fn is_undefined(&self) -> bool {
        self.d == 0 || (self.n == 0 && self.d == 1)
    }
    
    /// Parse decimal string DIRECTLY to Ratio.
    /// NO IEEE 754 INVOLVED AT ANY POINT!
    pub fn from_decimal_str(s: &str) -> Option<Self> {
        let s = s.trim();
        let parts: Vec<&str> = s.split('.').collect();
        
        match parts.len() {
            1 => {
                let n: u32 = parts[0].parse().ok()?;
                Some(Ratio::new(n, 1))
            }
            2 => {
                let whole_str = parts[0];
                let frac_str = parts[1];
                
                let decimals = frac_str.len() as u32;
                let denom = 10u32.checked_pow(decimals)?;
                
                let whole: u32 = if whole_str.is_empty() { 0 } else { whole_str.parse().ok()? };
                let frac: u32 = if frac_str.is_empty() { 0 } else { frac_str.parse().ok()? };
                
                let n = whole.checked_mul(denom)?.checked_add(frac)?;
                Some(Ratio::new(n, denom))
            }
            _ => None
        }
    }
    
    /// Cross-multiplication comparison: a/b >= c/d <=> a*d >= c*b
    /// NO DIVISION! This is the key to finite arithmetic.
    /// 
    /// FIX v0.5: Now takes Resources to track both budget AND heat
    pub fn ge(&self, other: &Ratio, res: &mut Resources) -> Option<bool> {
        res.spend(1)?;  // Uses Resources.spend which tracks heat
        let left = self.n as u64 * other.d as u64;
        let right = other.n as u64 * self.d as u64;
        Some(left >= right)
    }
    
    /// Greater than comparison
    /// FIX v0.5: Now takes Resources
    pub fn gt(&self, other: &Ratio, res: &mut Resources) -> Option<bool> {
        res.spend(1)?;
        let left = self.n as u64 * other.d as u64;
        let right = other.n as u64 * self.d as u64;
        Some(left > right)
    }
    
    /// Display as decimal string (for human eyes only!)
    pub fn to_decimal_string(&self, precision: usize) -> String {
        if self.d == 0 { return "0".to_string(); }
        
        let whole = self.n / self.d;
        let remainder = self.n % self.d;
        
        if remainder == 0 || precision == 0 {
            return whole.to_string();
        }
        
        let mut frac_str = String::new();
        let mut rem = remainder;
        for _ in 0..precision {
            rem *= 10;
            frac_str.push_str(&(rem / self.d).to_string());
            rem %= self.d;
            if rem == 0 { break; }
        }
        
        format!("{}.{}", whole, frac_str)
    }
    
    /// Display as percentage (for human eyes only!)
    pub fn to_percent_string(&self, precision: usize) -> String {
        if self.d == 0 { return "0%".to_string(); }
        
        let percent_n = self.n as u64 * 100;
        let percent_d = self.d as u64;
        
        let whole = percent_n / percent_d;
        let remainder = percent_n % percent_d;
        
        if remainder == 0 || precision == 0 {
            return format!("{}%", whole);
        }
        
        let mut frac_str = String::new();
        let mut rem = remainder;
        for _ in 0..precision {
            rem *= 10;
            frac_str.push_str(&(rem / percent_d).to_string());
            rem %= percent_d;
            if rem == 0 { break; }
        }
        
        format!("{}.{}%", whole, frac_str)
    }
    
    /// Display as fraction string
    pub fn to_fraction_string(&self) -> String {
        format!("{}/{}", self.n, self.d)
    }
    
    /// Simplify the ratio using GCD
    pub fn simplified(&self) -> Self {
        let g = gcd(self.n, self.d);
        if g == 0 { return *self; }
        Ratio::new(self.n / g, self.d / g)
    }
}

/// Greatest Common Divisor (Euclidean algorithm)
fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ============================================
// ENTROPY MAP - void_entropy.v (FIXED OVERFLOW)
// ============================================

/// EntropyMap tracks global symptom rarity.
/// FIX v0.5: Uses saturating_mul to prevent overflow
pub struct EntropyMap {
    pub symptom_counts: Vec<u32>,
    pub total_samples: u32,
    pub scale: u32,
}

impl EntropyMap {
    pub fn new(num_symptoms: usize) -> Self {
        EntropyMap {
            symptom_counts: vec![0; num_symptoms],
            total_samples: 0,
            scale: 1000,
        }
    }

    pub fn train(&mut self, patterns: &[Pattern]) {
        self.total_samples = patterns.len() as u32;
        
        for p in patterns {
            for (i, &present) in p.symptoms.iter().enumerate() {
                if present {
                    if i >= self.symptom_counts.len() {
                        self.symptom_counts.resize(i + 1, 0);
                    }
                    self.symptom_counts[i] = self.symptom_counts[i].saturating_add(1);
                }
            }
        }
        
        // Debug output
        let mut rarity: Vec<(usize, u32)> = self.symptom_counts.iter()
            .enumerate()
            .filter(|(_, &c)| c > 0)
            .map(|(i, &c)| (i, c))
            .collect();
        rarity.sort_by_key(|(_, c)| *c);
        
        println!("\n[EntropyMap] Trained on {} patterns (scale={})", self.total_samples, self.scale);
        println!("[EntropyMap] Top 5 RAREST symptoms:");
        for (i, (idx, count)) in rarity.iter().take(5).enumerate() {
            let weight = self.get_weight(*idx);
            println!("  {}. symptom[{}]: count={}, weight={}", i+1, idx, count, weight);
        }
        println!("[EntropyMap] Top 5 COMMON symptoms:");
        for (i, (idx, count)) in rarity.iter().rev().take(5).enumerate() {
            let weight = self.get_weight(*idx);
            println!("  {}. symptom[{}]: count={}, weight={}", i+1, idx, count, weight);
        }
        println!();
    }

    /// Get integer weight for symptom.
    /// FIX v0.5: Uses u64 intermediate to prevent overflow, then saturating conversion
    pub fn get_weight(&self, symptom_idx: usize) -> u32 {
        let count = self.symptom_counts.get(symptom_idx).copied().unwrap_or(0);
        // FIX: compute in u64 to prevent overflow
        let numerator = (self.scale as u64).saturating_mul(self.total_samples as u64);
        let denominator = (count as u64).saturating_add(1);
        let result = numerator / denominator;
        // Clamp to u32
        result.min(u32::MAX as u64) as u32
    }
}

// ============================================
// PATTERN
// ============================================

#[derive(Debug, Clone)]
pub struct Pattern {
    pub name: String,
    pub symptoms: Vec<bool>,
    pub strength: u32,
}

impl Pattern {
    pub fn new(name: String, symptoms: Vec<bool>) -> Self {
        Pattern { name, symptoms, strength: 1 }
    }
    
    /// Entropy-weighted comparison returning Ratio
    /// FIX v0.5: Uses Resources instead of separate budget/heat
    pub fn compare(&self, other: &[bool], entropy: &EntropyMap, res: &mut Resources) -> Option<Ratio> {
        let mut intersection_score: u64 = 0;
        let mut union_score: u64 = 0;
        
        for (i, (a, b)) in self.symptoms.iter().zip(other.iter()).enumerate() {
            res.spend(1)?;  // FIX: uses Resources.spend which tracks heat
            
            let weight = entropy.get_weight(i) as u64;
            let a_present = *a;
            let b_present = *b;
            
            if a_present || b_present {
                union_score = union_score.saturating_add(weight);
                if a_present && b_present {
                    intersection_score = intersection_score.saturating_add(weight);
                }
            }
        }
        
        let n = intersection_score.min(u32::MAX as u64) as u32;
        let d = union_score.min(u32::MAX as u64) as u32;
        
        Some(Ratio::new(n, d))
    }
}

// ============================================
// ORBIT
// ============================================

#[derive(Debug, Clone)]
pub struct Orbit {
    pub pattern: Pattern,
    pub hits: u32,
    pub misses: u32,
}

impl Orbit {
    pub fn new(pattern: Pattern) -> Self {
        Orbit { pattern, hits: 0, misses: 0 }
    }
    
    pub fn strength(&self) -> Ratio {
        let total = self.hits.saturating_add(self.misses);
        if total == 0 {
            Ratio::new(1, 1)
        } else {
            Ratio::new(self.hits, total)
        }
    }
    
    pub fn record_hit(&mut self) {
        self.hits = self.hits.saturating_add(1);
    }
    
    pub fn record_miss(&mut self) {
        self.misses = self.misses.saturating_add(1);
    }
}

// ============================================
// VOID NETWORK
// ============================================

pub struct VoidNetwork {
    pub orbits: Vec<Orbit>,
    pub max_orbits: usize,
    pub memory_bank: Vec<Pattern>,
    pub entropy: EntropyMap,
    
    pub match_threshold: Ratio,
    pub demotion_threshold: Ratio,
    pub alloc_cost: u32,
}

/// Result of memory bank search
/// FIX v0.5: Now includes exhausted flag and patterns_checked
struct SearchResult {
    best_match: Option<(String, Ratio, usize)>,
    exhausted: bool,
    patterns_checked: u32,
}

#[derive(Debug)]
pub enum InferenceResult {
    Match { 
        diagnosis: String, 
        confidence: Ratio,
        budget_spent: u32,
        heat_generated: u32,
    },
    DontKnow { 
        budget_spent: u32, 
        patterns_checked: u32,
        heat_generated: u32,
    },
    Exhausted { 
        partial_best: Option<(String, Ratio)>,  // FIX: now includes confidence
        budget_spent: u32,
        patterns_checked: u32,
        heat_generated: u32,
    },
}

impl VoidNetwork {
    pub fn new() -> Self {
        VoidNetwork {
            orbits: Vec::new(),
            max_orbits: 7,
            memory_bank: Vec::new(),
            entropy: EntropyMap::new(0),
            match_threshold: Ratio::from_decimal_str("0.5").unwrap(),
            demotion_threshold: Ratio::from_decimal_str("0.3").unwrap(),
            alloc_cost: 10,
        }
    }
    
    pub fn with_threshold(threshold: &str) -> Self {
        let mut net = VoidNetwork::new();
        if let Some(t) = Ratio::from_decimal_str(threshold) {
            net.match_threshold = t;
        }
        net
    }
    
    pub fn load_patterns_free(&mut self, patterns: Vec<Pattern>) {
        let num_symptoms = patterns.get(0).map(|p| p.symptoms.len()).unwrap_or(0);
        self.entropy = EntropyMap::new(num_symptoms);
        self.entropy.train(&patterns);
        self.memory_bank = patterns;
        println!("Loaded {} patterns into memory bank", self.memory_bank.len());
    }
    
    fn transduce(&self, symptoms: Vec<bool>, res: &mut Resources) -> Option<Vec<bool>> {
        res.spend(1)?;
        Some(symptoms)
    }
    
    fn check_orbits(&mut self, input: &[bool], res: &mut Resources) -> Option<(String, Ratio)> {
        for orbit in &mut self.orbits {
            if let Some(confidence) = orbit.pattern.compare(input, &self.entropy, res) {
                match confidence.ge(&self.match_threshold, res) {
                    Some(true) => {
                        orbit.record_hit();
                        println!("    [ORBIT HIT] {} (confidence: {} = {})", 
                                 orbit.pattern.name, 
                                 confidence.to_fraction_string(),
                                 confidence.to_percent_string(1));
                        return Some((orbit.pattern.name.clone(), confidence));
                    }
                    Some(false) => {
                        orbit.record_miss();
                    }
                    None => {
                        return None;  // Budget exhausted
                    }
                }
            } else {
                return None;  // Budget exhausted
            }
        }
        None
    }
    
    /// FIX v0.5: Returns SearchResult with exhausted flag and accurate patterns_checked
    fn search_memory_bank(&mut self, input: &[bool], res: &mut Resources) -> SearchResult {
        let mut best_match: Option<(String, Ratio, usize)> = None;
        let debug_threshold = Ratio::from_decimal_str("0.3").unwrap();
        let mut patterns_checked: u32 = 0;
        let mut exhausted = false;
        
        for (idx, pattern) in self.memory_bank.iter().enumerate() {
            if res.is_exhausted() {
                exhausted = true;
                break;
            }
            
            if let Some(confidence) = pattern.compare(input, &self.entropy, res) {
                patterns_checked = patterns_checked.saturating_add(1);
                
                if let Some(true) = confidence.gt(&debug_threshold, res) {
                    println!("    [DEBUG] {} → {} = {}",
                             pattern.name, 
                             confidence.to_fraction_string(),
                             confidence.to_percent_string(1));
                }
                
                match confidence.ge(&self.match_threshold, res) {
                    Some(true) => {
                        let dominated = if let Some((_, ref best_conf, _)) = best_match {
                            confidence.gt(best_conf, res).unwrap_or(false)
                        } else {
                            true
                        };
                        
                        if dominated {
                            best_match = Some((pattern.name.clone(), confidence, idx));
                        }
                    }
                    Some(false) => {}
                    None => {
                        exhausted = true;
                        break;
                    }
                }
            } else {
                exhausted = true;
                break;
            }
        }
        
        SearchResult {
            best_match,
            exhausted,
            patterns_checked,
        }
    }
    
    fn maybe_promote(&mut self, pattern_idx: usize, res: &mut Resources) {
        if res.spend(self.alloc_cost).is_none() {
            println!("  → Cannot promote (insufficient budget)");
            return;
        }
        
        if self.orbits.len() < self.max_orbits {
            let pattern = self.memory_bank[pattern_idx].clone();
            self.orbits.push(Orbit::new(pattern));
            println!("  → Promoted '{}' to working memory", self.memory_bank[pattern_idx].name);
        } else {
            let mut weakest_idx = 0;
            let mut weakest_strength = self.orbits[0].strength();
            
            for (i, orbit) in self.orbits.iter().enumerate().skip(1) {
                let strength = orbit.strength();
                if let Some(true) = weakest_strength.gt(&strength, res) {
                    weakest_idx = i;
                    weakest_strength = strength;
                }
            }
            
            if let Some(true) = self.demotion_threshold.gt(&weakest_strength, res) {
                let demoted = self.orbits.remove(weakest_idx);
                println!("  → Demoted '{}' (strength: {})", 
                         demoted.pattern.name, weakest_strength.to_fraction_string());
                
                let pattern = self.memory_bank[pattern_idx].clone();
                self.orbits.push(Orbit::new(pattern));
                println!("  → Promoted '{}' to working memory", self.memory_bank[pattern_idx].name);
            }
        }
    }
    
    pub fn infer(&mut self, symptoms: Vec<bool>, initial_budget: u32) -> InferenceResult {
        let mut res = Resources::new(initial_budget);
        
        // LAYER 1: Transduction
        let input = match self.transduce(symptoms, &mut res) {
            Some(p) => p,
            None => return InferenceResult::Exhausted { 
                partial_best: None, 
                budget_spent: initial_budget,
                patterns_checked: 0,
                heat_generated: res.heat_total(),
            },
        };
        
        // LAYER 2: Check orbits (CHEAP)
        let orbits_count = self.orbits.len() as u32;
        if let Some((diagnosis, confidence)) = self.check_orbits(&input, &mut res) {
            return InferenceResult::Match {
                diagnosis,
                confidence,
                budget_spent: initial_budget - res.remaining(),
                heat_generated: res.heat_total(),
            };
        }
        
        // LAYER 3: Search memory bank (EXPENSIVE)
        let search_result = self.search_memory_bank(&input, &mut res);
        let total_patterns_checked = orbits_count.saturating_add(search_result.patterns_checked);
        
        // FIX v0.5: If exhausted during search but found partial match → Exhausted, not Match
        if search_result.exhausted {
            return InferenceResult::Exhausted {
                partial_best: search_result.best_match.map(|(name, conf, _)| (name, conf)),
                budget_spent: initial_budget - res.remaining(),
                patterns_checked: total_patterns_checked,
                heat_generated: res.heat_total(),
            };
        }
        
        // Not exhausted - check if we found a match
        if let Some((diagnosis, confidence, idx)) = search_result.best_match {
            // LAYER 4: Maybe promote
            self.maybe_promote(idx, &mut res);
            
            return InferenceResult::Match {
                diagnosis,
                confidence,
                budget_spent: initial_budget - res.remaining(),
                heat_generated: res.heat_total(),
            };
        }
        
        // No match found, not exhausted → genuinely don't know
        InferenceResult::DontKnow {
            budget_spent: initial_budget - res.remaining(),
            patterns_checked: total_patterns_checked,
            heat_generated: res.heat_total(),
        }
    }
    
    pub fn status(&self) {
        println!("\n=== VOID Network Status (AUDITED v0.5) ===");
        println!("Working Memory (Orbits): {}/{}", self.orbits.len(), self.max_orbits);
        for (i, orbit) in self.orbits.iter().enumerate() {
            let strength = orbit.strength();
            println!("  [{}] {} (strength: {} = {}, hits: {}, misses: {})", 
                     i, orbit.pattern.name, 
                     strength.to_fraction_string(),
                     strength.to_percent_string(1),
                     orbit.hits, orbit.misses);
        }
        println!("Memory Bank: {} patterns", self.memory_bank.len());
        println!("Match Threshold: {} = {}", 
                 self.match_threshold.to_fraction_string(),
                 self.match_threshold.to_percent_string(1));
        println!("================================================\n");
    }
}

// ============================================
// DATA LOADING
// ============================================

fn load_csv(path: &str) -> Result<Vec<Pattern>, Box<dyn std::error::Error>> {
    let file = File::open(path)?;
    let mut reader = csv::Reader::from_reader(BufReader::new(file));
    
    let mut patterns = Vec::new();
    
    for result in reader.records() {
        let record = result?;
        let diagnosis = record.get(0).unwrap_or("unknown").to_string();
        let symptoms: Vec<bool> = record.iter()
            .skip(1)
            .map(|s| s == "1")
            .collect();
        patterns.push(Pattern::new(diagnosis, symptoms));
    }
    
    Ok(patterns)
}

// ============================================
// MAIN
// ============================================

fn main() {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║      VOID Neural Network v0.5 - AUDITED                    ║");
    println!("║  Fixes: Heat tracking, entropy overflow, exhausted+match   ║");
    println!("║  All budget spends now generate heat                       ║");
    println!("║  'I don't know' is a valid answer                         ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");
    
    println!("AUDIT FIXES (GPT-5.2):");
    println!("  ✓ Heat tracks ALL budget spends (including ge/gt)");
    println!("  ✓ Entropy weight uses u64 intermediate (no overflow)");
    println!("  ✓ Match during exhaustion → Exhausted with partial_best");
    println!("  ✓ patterns_checked is now accurate");
    println!();
    
    // Demo: parsing decimal strings
    println!("=== Ratio from decimal strings (NO FLOATS) ===");
    let examples = ["0.5", "0.625", "0.333", "1.0", "0.1"];
    for s in examples {
        if let Some(r) = Ratio::from_decimal_str(s) {
            let simplified = r.simplified();
            println!("  \"{}\" → {} → simplified: {} = {}", 
                     s, r.to_fraction_string(), 
                     simplified.to_fraction_string(),
                     simplified.to_percent_string(2));
        }
    }
    println!();
    
    // Load data
    let patterns = match load_csv("disease_symptoms_sample.csv") {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error loading data: {}", e);
            return;
        }
    };
    
    println!("Loaded {} disease patterns\n", patterns.len());
    
    // Create network
    let mut network = VoidNetwork::new();
    
    // Split data
    let train_size = 800.min(patterns.len());
    let (train, test) = patterns.split_at(train_size);
    
    network.load_patterns_free(train.to_vec());
    network.status();
    
    // Test inference
    println!("=== Testing Inference (AUDITED v0.5) ===\n");
    
    let mut correct = 0u32;
    let mut wrong = 0u32;
    let mut dont_know = 0u32;
    let mut exhausted = 0u32;
    
    for (i, test_pattern) in test.iter().take(10).enumerate() {
        let budget = 500000;
        
        println!("Test {}: Looking for '{}'", i + 1, test_pattern.name);
        
        let result = network.infer(test_pattern.symptoms.clone(), budget);
        
        match result {
            InferenceResult::Match { diagnosis, confidence, budget_spent, heat_generated } => {
                let is_correct = diagnosis == test_pattern.name;
                println!("  → Match: {} (confidence: {} = {})", 
                         diagnosis, 
                         confidence.to_fraction_string(),
                         confidence.to_percent_string(1));
                println!("  → Budget: {}, Heat: {}", budget_spent, heat_generated);
                if is_correct {
                    println!("  → ✓ CORRECT");
                    correct = correct.saturating_add(1);
                } else {
                    println!("  → ✗ WRONG (but may be medically related)");
                    wrong = wrong.saturating_add(1);
                }
            }
            InferenceResult::DontKnow { budget_spent, patterns_checked, heat_generated } => {
                println!("  → I DON'T KNOW (checked {} patterns)", patterns_checked);
                println!("  → Budget: {}, Heat: {}", budget_spent, heat_generated);
                println!("  → This is honest - no confident match found");
                dont_know = dont_know.saturating_add(1);
            }
            InferenceResult::Exhausted { partial_best, budget_spent, patterns_checked, heat_generated } => {
                print!("  → EXHAUSTED (checked {} patterns", patterns_checked);
                if let Some((name, conf)) = partial_best {
                    println!(", partial: {} at {})", name, conf.to_percent_string(1));
                } else {
                    println!(", no partial match)");
                }
                println!("  → Budget: {}, Heat: {}", budget_spent, heat_generated);
                exhausted = exhausted.saturating_add(1);
            }
        }
        println!();
    }
    
    // Final status
    network.status();
    
    println!("═══════════════════════════════════════════════════════════════");
    println!("RESULTS: {} correct, {} wrong, {} 'I don't know', {} exhausted", 
             correct, wrong, dont_know, exhausted);
    println!("═══════════════════════════════════════════════════════════════");
    println!();
    println!("v0.5 AUDIT COMPLETE:");
    println!("- Heat = Budget spent (now enforced via Resources struct)");
    println!("- Entropy overflow prevented (u64 intermediate)");
    println!("- Exhausted during match → Exhausted, not Match");
    println!();
    println!("Maat weighs ratios AND tracks heat. Pascal's floats can go to hell.");
}
