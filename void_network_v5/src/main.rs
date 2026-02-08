//! VOID Neural Network v0.6 - LEARNING
//! 
//! NEW IN v0.6:
//! - Network learns from mistakes (adds correct pattern to memory bank)
//! - Learning costs budget - not free!
//! - Multiple epochs show improvement over time
//!
//! AUDIT FIXES (from v0.5):
//! - Heat tracks ALL budget spends
//! - Entropy weight uses u64 intermediate (no overflow)
//! - Match during exhaustion → Exhausted with partial_best

use std::fs::File;
use std::io::BufReader;

// ============================================
// CORE TYPES - STRICTLY FINITE
// ============================================

#[derive(Debug, Clone, Copy)]
pub struct Budget(u32);

impl Budget {
    pub fn new(initial: u32) -> Self {
        Budget(initial)
    }
    
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
    
    pub fn spend(&mut self, cost: u32) -> Option<u32> {
        let result = self.budget.spend(cost)?;
        self.heat.add(cost);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ratio {
    pub n: u32,
    pub d: u32,
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
    
    pub fn ge(&self, other: &Ratio, res: &mut Resources) -> Option<bool> {
        res.spend(1)?;
        let left = self.n as u64 * other.d as u64;
        let right = other.n as u64 * self.d as u64;
        Some(left >= right)
    }
    
    pub fn gt(&self, other: &Ratio, res: &mut Resources) -> Option<bool> {
        res.spend(1)?;
        let left = self.n as u64 * other.d as u64;
        let right = other.n as u64 * self.d as u64;
        Some(left > right)
    }
    
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
    
    pub fn to_fraction_string(&self) -> String {
        format!("{}/{}", self.n, self.d)
    }
    
    pub fn simplified(&self) -> Self {
        let g = gcd(self.n, self.d);
        if g == 0 { return *self; }
        Ratio::new(self.n / g, self.d / g)
    }
}

fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ============================================
// ENTROPY MAP
// ============================================

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
        
        // Reset counts
        for c in &mut self.symptom_counts {
            *c = 0;
        }
        
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
    }

    pub fn get_weight(&self, symptom_idx: usize) -> u32 {
        let count = self.symptom_counts.get(symptom_idx).copied().unwrap_or(0);
        let numerator = (self.scale as u64).saturating_mul(self.total_samples as u64);
        let denominator = (count as u64).saturating_add(1);
        let result = numerator / denominator;
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
    
    pub fn compare(&self, other: &[bool], entropy: &EntropyMap, res: &mut Resources) -> Option<Ratio> {
        let mut intersection_score: u64 = 0;
        let mut union_score: u64 = 0;
        
        for (i, (a, b)) in self.symptoms.iter().zip(other.iter()).enumerate() {
            res.spend(1)?;
            
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
    pub learning_cost: u32,
}

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
        partial_best: Option<(String, Ratio)>,
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
            learning_cost: 50,  // Learning costs budget!
        }
    }
    
    pub fn load_patterns_free(&mut self, patterns: Vec<Pattern>) {
        let num_symptoms = patterns.get(0).map(|p| p.symptoms.len()).unwrap_or(0);
        self.entropy = EntropyMap::new(num_symptoms);
        self.entropy.train(&patterns);
        self.memory_bank = patterns;
    }
    
    /// Retrain entropy map after learning new patterns
    pub fn retrain_entropy(&mut self) {
        self.entropy.train(&self.memory_bank);
    }
    
    /// LEARN FROM MISTAKE
    /// Adds correct pattern to memory bank
    /// Returns true if learned, false if pattern already exists or out of budget
    pub fn learn(&mut self, pattern: Pattern, res: &mut Resources) -> bool {
        // Check if we already know this exact pattern
        for p in &self.memory_bank {
            if p.name == pattern.name && p.symptoms == pattern.symptoms {
                return false; // Already known
            }
        }
        
        // Learning costs budget!
        if res.spend(self.learning_cost).is_none() {
            return false;
        }
        
        self.memory_bank.push(pattern);
        true
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
                        return Some((orbit.pattern.name.clone(), confidence));
                    }
                    Some(false) => {
                        orbit.record_miss();
                    }
                    None => {
                        return None;
                    }
                }
            } else {
                return None;
            }
        }
        None
    }
    
    fn search_memory_bank(&mut self, input: &[bool], res: &mut Resources) -> SearchResult {
        let mut best_match: Option<(String, Ratio, usize)> = None;
        let mut patterns_checked: u32 = 0;
        let mut exhausted = false;
        
        for (idx, pattern) in self.memory_bank.iter().enumerate() {
            if res.is_exhausted() {
                exhausted = true;
                break;
            }
            
            if let Some(confidence) = pattern.compare(input, &self.entropy, res) {
                patterns_checked = patterns_checked.saturating_add(1);
                
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
            return;
        }
        
        if self.orbits.len() < self.max_orbits {
            let pattern = self.memory_bank[pattern_idx].clone();
            self.orbits.push(Orbit::new(pattern));
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
                self.orbits.remove(weakest_idx);
                let pattern = self.memory_bank[pattern_idx].clone();
                self.orbits.push(Orbit::new(pattern));
            }
        }
    }
    
    pub fn infer(&mut self, symptoms: Vec<bool>, initial_budget: u32) -> InferenceResult {
        let mut res = Resources::new(initial_budget);
        
        let input = match self.transduce(symptoms, &mut res) {
            Some(p) => p,
            None => return InferenceResult::Exhausted { 
                partial_best: None, 
                budget_spent: initial_budget,
                patterns_checked: 0,
                heat_generated: res.heat_total(),
            },
        };
        
        let orbits_count = self.orbits.len() as u32;
        if let Some((diagnosis, confidence)) = self.check_orbits(&input, &mut res) {
            return InferenceResult::Match {
                diagnosis,
                confidence,
                budget_spent: initial_budget - res.remaining(),
                heat_generated: res.heat_total(),
            };
        }
        
        let search_result = self.search_memory_bank(&input, &mut res);
        let total_patterns_checked = orbits_count.saturating_add(search_result.patterns_checked);
        
        if search_result.exhausted {
            return InferenceResult::Exhausted {
                partial_best: search_result.best_match.map(|(name, conf, _)| (name, conf)),
                budget_spent: initial_budget - res.remaining(),
                patterns_checked: total_patterns_checked,
                heat_generated: res.heat_total(),
            };
        }
        
        if let Some((diagnosis, confidence, idx)) = search_result.best_match {
            self.maybe_promote(idx, &mut res);
            
            return InferenceResult::Match {
                diagnosis,
                confidence,
                budget_spent: initial_budget - res.remaining(),
                heat_generated: res.heat_total(),
            };
        }
        
        InferenceResult::DontKnow {
            budget_spent: initial_budget - res.remaining(),
            patterns_checked: total_patterns_checked,
            heat_generated: res.heat_total(),
        }
    }
    
    /// Infer with learning - returns remaining resources for potential learning
    pub fn infer_with_resources(&mut self, symptoms: Vec<bool>, res: &mut Resources) -> InferenceResult {
        let initial_budget = res.remaining();
        
        let input = match self.transduce(symptoms, res) {
            Some(p) => p,
            None => return InferenceResult::Exhausted { 
                partial_best: None, 
                budget_spent: initial_budget - res.remaining(),
                patterns_checked: 0,
                heat_generated: res.heat_total(),
            },
        };
        
        let orbits_count = self.orbits.len() as u32;
        if let Some((diagnosis, confidence)) = self.check_orbits(&input, res) {
            return InferenceResult::Match {
                diagnosis,
                confidence,
                budget_spent: initial_budget - res.remaining(),
                heat_generated: res.heat_total(),
            };
        }
        
        let search_result = self.search_memory_bank(&input, res);
        let total_patterns_checked = orbits_count.saturating_add(search_result.patterns_checked);
        
        if search_result.exhausted {
            return InferenceResult::Exhausted {
                partial_best: search_result.best_match.map(|(name, conf, _)| (name, conf)),
                budget_spent: initial_budget - res.remaining(),
                patterns_checked: total_patterns_checked,
                heat_generated: res.heat_total(),
            };
        }
        
        if let Some((diagnosis, confidence, idx)) = search_result.best_match {
            self.maybe_promote(idx, res);
            
            return InferenceResult::Match {
                diagnosis,
                confidence,
                budget_spent: initial_budget - res.remaining(),
                heat_generated: res.heat_total(),
            };
        }
        
        InferenceResult::DontKnow {
            budget_spent: initial_budget - res.remaining(),
            patterns_checked: total_patterns_checked,
            heat_generated: res.heat_total(),
        }
    }
    
    pub fn status(&self) {
        println!("\n=== VOID Network Status (v0.6 LEARNING) ===");
        println!("Working Memory (Orbits): {}/{}", self.orbits.len(), self.max_orbits);
        println!("Memory Bank: {} patterns", self.memory_bank.len());
        println!("Match Threshold: {} = {}", 
                 self.match_threshold.to_fraction_string(),
                 self.match_threshold.to_percent_string(1));
        println!("Learning Cost: {} budget per pattern", self.learning_cost);
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
    println!("║      VOID Neural Network v0.6 - LEARNING                   ║");
    println!("║  Network learns from mistakes (costs budget!)              ║");
    println!("║  Multiple epochs show improvement                          ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");
    
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
    
    // Split data: 800 train, rest test
    let train_size = 800.min(patterns.len());
    let (train, test) = patterns.split_at(train_size);
    
    network.load_patterns_free(train.to_vec());
    
    println!("Training set: {} patterns", train.len());
    println!("Test set: {} patterns\n", test.len());
    
    // Run multiple epochs
    let num_epochs = 3;
    
    for epoch in 1..=num_epochs {
        println!("═══════════════════════════════════════════════════════════════");
        println!("                        EPOCH {}", epoch);
        println!("═══════════════════════════════════════════════════════════════\n");
        
        let mut correct = 0u32;
        let mut wrong = 0u32;
        let mut dont_know = 0u32;
        let mut learned = 0u32;
        
        for test_pattern in test.iter() {
            let mut res = Resources::new(500000);
            
            let result = network.infer_with_resources(test_pattern.symptoms.clone(), &mut res);
            
            match result {
                InferenceResult::Match { diagnosis, .. } => {
                    let is_correct = diagnosis == test_pattern.name;
                    if is_correct {
                        correct = correct.saturating_add(1);
                    } else {
                        wrong = wrong.saturating_add(1);
                        // LEARN FROM MISTAKE!
                        if network.learn(test_pattern.clone(), &mut res) {
                            learned = learned.saturating_add(1);
                        }
                    }
                }
                InferenceResult::DontKnow { .. } => {
                    dont_know = dont_know.saturating_add(1);
                    // Also learn from "I don't know" - these are missed patterns
                    if network.learn(test_pattern.clone(), &mut res) {
                        learned = learned.saturating_add(1);
                    }
                }
                InferenceResult::Exhausted { .. } => {
                    // Don't count exhausted
                }
            }
        }
        
        // Retrain entropy after learning
        if learned > 0 {
            network.retrain_entropy();
        }
        
        let total_answered = correct + wrong;
        let accuracy_when_answers = if total_answered > 0 {
            (correct as f64 / total_answered as f64) * 100.0
        } else {
            0.0
        };
        
        println!("EPOCH {} RESULTS:", epoch);
        println!("  Correct: {}", correct);
        println!("  Wrong: {}", wrong);
        println!("  Don't know: {}", dont_know);
        println!("  Learned: {} new patterns", learned);
        println!("  Memory bank size: {}", network.memory_bank.len());
        println!("  Accuracy (when answering): {:.1}%", accuracy_when_answers);
        println!();
    }
    
    network.status();
    
    println!("v0.6 LEARNING COMPLETE:");
    println!("- Network learns from mistakes");
    println!("- Learning costs {} budget per pattern", network.learning_cost);
    println!("- Entropy recomputed after each epoch");
    println!();
    println!("Maat weighs ratios, tracks heat, and learns from failure.");
}
