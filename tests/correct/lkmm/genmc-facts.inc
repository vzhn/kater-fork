// Facts about GenMC's labels that Kater cannot read from the predicates' C++
// strings in lkmm-genmc.kat. Each holds by construction in GenMC 0.19:
// Acq, R4rmb, MbR and LKR are ReadLabels, Rel, MbW, LKW, UL and SrcuU
// WriteLabels; the kernel's ordered accesses, fences, locks and RMWs carry
// an atomic ordering.

// reads, writes and fences
disjoint R # W # F
disjoint lkmm-genmc::Acq # W # F
disjoint lkmm-genmc::R4rmb # W # F
disjoint lkmm-genmc::MbR # W # F
disjoint lkmm-genmc::LKR # W # F
disjoint lkmm-genmc::Rel # R # F
disjoint lkmm-genmc::MbW # R # F
disjoint lkmm-genmc::LKW # R # F
disjoint lkmm-genmc::UL # R # F
disjoint lkmm-genmc::SrcuU # R # F

// atomic orderings
disjoint lkmm-genmc::Acq # NA
disjoint lkmm-genmc::Rel # NA
disjoint lkmm-genmc::MbR # NA
disjoint lkmm-genmc::MbW # NA
disjoint lkmm-genmc::LKR # NA
disjoint lkmm-genmc::LKW # NA
disjoint lkmm-genmc::UL # NA
disjoint F # NA
disjoint EXCL # NA
