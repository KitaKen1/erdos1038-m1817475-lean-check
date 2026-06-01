import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block412

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block412

open Set

def block412W1 : Rat := ((1779684339050101 : Rat) / 2500000000000000)
def block412W2 : Rat := (0 : Rat)
def block412W3 : Rat := ((14416667448164183 : Rat) / 50000000000000000)
def block412W4 : Rat := ((2217630640861673 : Rat) / 25000000000000000)
def block412S1 : Rat := ((18174751 : Rat) / 10000000)
def block412S2 : Rat := ((511587 : Rat) / 200000)
def block412S3 : Rat := ((132079325089285714359 : Rat) / 50000000000000000000)
def block412S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block412V (y : ℝ) : ℝ :=
  ratPotential block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4 y

def block412LeftParamsCertificate : Bool :=
  allBoxesSameParams block412LeftBoxes block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4

theorem block412LeftParamsCertificate_eq_true :
    block412LeftParamsCertificate = true := by
  native_decide

theorem block412_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412LeftL : ℝ) (block412LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  have hcert := block412LeftCertificate_eq_true
  unfold block412LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block412LeftBoxes) (lo := block412LeftL) (hi := block412LeftR)
    (w1 := block412W1) (w2 := block412W2) (w3 := block412W3) (w4 := block412W4)
    (s1 := block412S1) (s2 := block412S2) (s3 := block412S3) (s4 := block412S4)
    hboxes hcover block412LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block412RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block412RightChunk000 block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4

theorem block412RightChunk000ParamsCertificate_eq_true :
    block412RightChunk000ParamsCertificate = true := by
  native_decide

theorem block412_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412RightChunk000L : ℝ) (block412RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  have hcert := block412RightChunk000Certificate_eq_true
  unfold block412RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block412RightChunk000) (lo := block412RightChunk000L) (hi := block412RightChunk000R)
    (w1 := block412W1) (w2 := block412W2) (w3 := block412W3) (w4 := block412W4)
    (s1 := block412S1) (s2 := block412S2) (s3 := block412S3) (s4 := block412S4)
    hboxes hcover block412RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block412RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block412RightChunk001 block412W1 block412W2 block412W3 block412W4 block412S1 block412S2 block412S3 block412S4

theorem block412RightChunk001ParamsCertificate_eq_true :
    block412RightChunk001ParamsCertificate = true := by
  native_decide

theorem block412_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412RightChunk001L : ℝ) (block412RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  have hcert := block412RightChunk001Certificate_eq_true
  unfold block412RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block412RightChunk001) (lo := block412RightChunk001L) (hi := block412RightChunk001R)
    (w1 := block412W1) (w2 := block412W2) (w3 := block412W3) (w4 := block412W4)
    (s1 := block412S1) (s2 := block412S2) (s3 := block412S3) (s4 := block412S4)
    hboxes hcover block412RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block412_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block412RightL : ℝ) (block412RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block412S1 : ℝ))
    (hy2ne : y ≠ (block412S2 : ℝ))
    (hy3ne : y ≠ (block412S3 : ℝ))
    (hy4ne : y ≠ (block412S4 : ℝ)) :
    0 < block412V y := by
  by_cases h0 : y ≤ (block412RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block412RightChunk000L : ℝ) (block412RightChunk000R : ℝ) := by
      have hL : (block412RightChunk000L : ℝ) = (block412RightL : ℝ) := by
        norm_num [block412RightChunk000L, block412RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block412_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block412RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block412RightChunk001L : ℝ) = (block412RightChunk000R : ℝ) := by
      norm_num [block412RightChunk001L, block412RightChunk000R]
    have hR : (block412RightChunk001R : ℝ) = (block412RightR : ℝ) := by
      norm_num [block412RightChunk001R, block412RightR]
    have hyc : y ∈ Icc (block412RightChunk001L : ℝ) (block412RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block412_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block412_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block412LeftL : ℝ) (block412LeftR : ℝ) →
    y ≠ 0 → y ≠ (block412S1 : ℝ) → y ≠ (block412S2 : ℝ) →
    y ≠ (block412S3 : ℝ) → y ≠ (block412S4 : ℝ) → 0 < block412V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block412RightL : ℝ) (block412RightR : ℝ) →
    y ≠ 0 → y ≠ (block412S1 : ℝ) → y ≠ (block412S2 : ℝ) →
    y ≠ (block412S3 : ℝ) → y ≠ (block412S4 : ℝ) → 0 < block412V y)

theorem block412_reallog_certificate_proof :
    block412_reallog_certificate := by
  exact ⟨block412_left_V_pos, block412_right_V_pos⟩

end Block412
end M1817475
end Erdos1038Lean
