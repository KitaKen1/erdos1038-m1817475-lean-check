import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block258

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block258

open Set

def block258W1 : Rat := ((1113486803344487 : Rat) / 1250000000000000)
def block258W2 : Rat := ((1888537062917339 : Rat) / 25000000000000000)
def block258W3 : Rat := ((3905424625541773 : Rat) / 20000000000000000)
def block258W4 : Rat := ((787121905292223 : Rat) / 12500000000000000)
def block258S1 : Rat := ((18174751 : Rat) / 10000000)
def block258S2 : Rat := ((511587 : Rat) / 200000)
def block258S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block258S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block258V (y : ℝ) : ℝ :=
  ratPotential block258W1 block258W2 block258W3 block258W4 block258S1 block258S2 block258S3 block258S4 y

def block258LeftParamsCertificate : Bool :=
  allBoxesSameParams block258LeftBoxes block258W1 block258W2 block258W3 block258W4 block258S1 block258S2 block258S3 block258S4

theorem block258LeftParamsCertificate_eq_true :
    block258LeftParamsCertificate = true := by
  native_decide

theorem block258_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block258LeftL : ℝ) (block258LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block258S1 : ℝ))
    (hy2ne : y ≠ (block258S2 : ℝ))
    (hy3ne : y ≠ (block258S3 : ℝ))
    (hy4ne : y ≠ (block258S4 : ℝ)) :
    0 < block258V y := by
  have hcert := block258LeftCertificate_eq_true
  unfold block258LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block258LeftBoxes) (lo := block258LeftL) (hi := block258LeftR)
    (w1 := block258W1) (w2 := block258W2) (w3 := block258W3) (w4 := block258W4)
    (s1 := block258S1) (s2 := block258S2) (s3 := block258S3) (s4 := block258S4)
    hboxes hcover block258LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block258RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block258RightChunk000 block258W1 block258W2 block258W3 block258W4 block258S1 block258S2 block258S3 block258S4

theorem block258RightChunk000ParamsCertificate_eq_true :
    block258RightChunk000ParamsCertificate = true := by
  native_decide

theorem block258_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block258RightChunk000L : ℝ) (block258RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block258S1 : ℝ))
    (hy2ne : y ≠ (block258S2 : ℝ))
    (hy3ne : y ≠ (block258S3 : ℝ))
    (hy4ne : y ≠ (block258S4 : ℝ)) :
    0 < block258V y := by
  have hcert := block258RightChunk000Certificate_eq_true
  unfold block258RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block258RightChunk000) (lo := block258RightChunk000L) (hi := block258RightChunk000R)
    (w1 := block258W1) (w2 := block258W2) (w3 := block258W3) (w4 := block258W4)
    (s1 := block258S1) (s2 := block258S2) (s3 := block258S3) (s4 := block258S4)
    hboxes hcover block258RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block258RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block258RightChunk001 block258W1 block258W2 block258W3 block258W4 block258S1 block258S2 block258S3 block258S4

theorem block258RightChunk001ParamsCertificate_eq_true :
    block258RightChunk001ParamsCertificate = true := by
  native_decide

theorem block258_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block258RightChunk001L : ℝ) (block258RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block258S1 : ℝ))
    (hy2ne : y ≠ (block258S2 : ℝ))
    (hy3ne : y ≠ (block258S3 : ℝ))
    (hy4ne : y ≠ (block258S4 : ℝ)) :
    0 < block258V y := by
  have hcert := block258RightChunk001Certificate_eq_true
  unfold block258RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block258RightChunk001) (lo := block258RightChunk001L) (hi := block258RightChunk001R)
    (w1 := block258W1) (w2 := block258W2) (w3 := block258W3) (w4 := block258W4)
    (s1 := block258S1) (s2 := block258S2) (s3 := block258S3) (s4 := block258S4)
    hboxes hcover block258RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block258_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block258RightL : ℝ) (block258RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block258S1 : ℝ))
    (hy2ne : y ≠ (block258S2 : ℝ))
    (hy3ne : y ≠ (block258S3 : ℝ))
    (hy4ne : y ≠ (block258S4 : ℝ)) :
    0 < block258V y := by
  by_cases h0 : y ≤ (block258RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block258RightChunk000L : ℝ) (block258RightChunk000R : ℝ) := by
      have hL : (block258RightChunk000L : ℝ) = (block258RightL : ℝ) := by
        norm_num [block258RightChunk000L, block258RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block258_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block258RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block258RightChunk001L : ℝ) = (block258RightChunk000R : ℝ) := by
      norm_num [block258RightChunk001L, block258RightChunk000R]
    have hR : (block258RightChunk001R : ℝ) = (block258RightR : ℝ) := by
      norm_num [block258RightChunk001R, block258RightR]
    have hyc : y ∈ Icc (block258RightChunk001L : ℝ) (block258RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block258_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block258_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block258LeftL : ℝ) (block258LeftR : ℝ) →
    y ≠ 0 → y ≠ (block258S1 : ℝ) → y ≠ (block258S2 : ℝ) →
    y ≠ (block258S3 : ℝ) → y ≠ (block258S4 : ℝ) → 0 < block258V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block258RightL : ℝ) (block258RightR : ℝ) →
    y ≠ 0 → y ≠ (block258S1 : ℝ) → y ≠ (block258S2 : ℝ) →
    y ≠ (block258S3 : ℝ) → y ≠ (block258S4 : ℝ) → 0 < block258V y)

theorem block258_reallog_certificate_proof :
    block258_reallog_certificate := by
  exact ⟨block258_left_V_pos, block258_right_V_pos⟩

end Block258
end M1817475
end Erdos1038Lean
