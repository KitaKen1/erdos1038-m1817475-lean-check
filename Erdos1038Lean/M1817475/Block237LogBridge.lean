import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block237

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block237

open Set

def block237W1 : Rat := ((8625537053302667 : Rat) / 10000000000000000)
def block237W2 : Rat := ((4225725893279 : Rat) / 50000000000000)
def block237W3 : Rat := ((1811232955969187 : Rat) / 10000000000000000)
def block237W4 : Rat := ((7109472867072603 : Rat) / 100000000000000000)
def block237S1 : Rat := ((18174751 : Rat) / 10000000)
def block237S2 : Rat := ((511587 : Rat) / 200000)
def block237S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block237S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block237V (y : ℝ) : ℝ :=
  ratPotential block237W1 block237W2 block237W3 block237W4 block237S1 block237S2 block237S3 block237S4 y

def block237LeftParamsCertificate : Bool :=
  allBoxesSameParams block237LeftBoxes block237W1 block237W2 block237W3 block237W4 block237S1 block237S2 block237S3 block237S4

theorem block237LeftParamsCertificate_eq_true :
    block237LeftParamsCertificate = true := by
  native_decide

theorem block237_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block237LeftL : ℝ) (block237LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block237S1 : ℝ))
    (hy2ne : y ≠ (block237S2 : ℝ))
    (hy3ne : y ≠ (block237S3 : ℝ))
    (hy4ne : y ≠ (block237S4 : ℝ)) :
    0 < block237V y := by
  have hcert := block237LeftCertificate_eq_true
  unfold block237LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block237LeftBoxes) (lo := block237LeftL) (hi := block237LeftR)
    (w1 := block237W1) (w2 := block237W2) (w3 := block237W3) (w4 := block237W4)
    (s1 := block237S1) (s2 := block237S2) (s3 := block237S3) (s4 := block237S4)
    hboxes hcover block237LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block237RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block237RightChunk000 block237W1 block237W2 block237W3 block237W4 block237S1 block237S2 block237S3 block237S4

theorem block237RightChunk000ParamsCertificate_eq_true :
    block237RightChunk000ParamsCertificate = true := by
  native_decide

theorem block237_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block237RightChunk000L : ℝ) (block237RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block237S1 : ℝ))
    (hy2ne : y ≠ (block237S2 : ℝ))
    (hy3ne : y ≠ (block237S3 : ℝ))
    (hy4ne : y ≠ (block237S4 : ℝ)) :
    0 < block237V y := by
  have hcert := block237RightChunk000Certificate_eq_true
  unfold block237RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block237RightChunk000) (lo := block237RightChunk000L) (hi := block237RightChunk000R)
    (w1 := block237W1) (w2 := block237W2) (w3 := block237W3) (w4 := block237W4)
    (s1 := block237S1) (s2 := block237S2) (s3 := block237S3) (s4 := block237S4)
    hboxes hcover block237RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block237RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block237RightChunk001 block237W1 block237W2 block237W3 block237W4 block237S1 block237S2 block237S3 block237S4

theorem block237RightChunk001ParamsCertificate_eq_true :
    block237RightChunk001ParamsCertificate = true := by
  native_decide

theorem block237_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block237RightChunk001L : ℝ) (block237RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block237S1 : ℝ))
    (hy2ne : y ≠ (block237S2 : ℝ))
    (hy3ne : y ≠ (block237S3 : ℝ))
    (hy4ne : y ≠ (block237S4 : ℝ)) :
    0 < block237V y := by
  have hcert := block237RightChunk001Certificate_eq_true
  unfold block237RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block237RightChunk001) (lo := block237RightChunk001L) (hi := block237RightChunk001R)
    (w1 := block237W1) (w2 := block237W2) (w3 := block237W3) (w4 := block237W4)
    (s1 := block237S1) (s2 := block237S2) (s3 := block237S3) (s4 := block237S4)
    hboxes hcover block237RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block237_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block237RightL : ℝ) (block237RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block237S1 : ℝ))
    (hy2ne : y ≠ (block237S2 : ℝ))
    (hy3ne : y ≠ (block237S3 : ℝ))
    (hy4ne : y ≠ (block237S4 : ℝ)) :
    0 < block237V y := by
  by_cases h0 : y ≤ (block237RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block237RightChunk000L : ℝ) (block237RightChunk000R : ℝ) := by
      have hL : (block237RightChunk000L : ℝ) = (block237RightL : ℝ) := by
        norm_num [block237RightChunk000L, block237RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block237_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block237RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block237RightChunk001L : ℝ) = (block237RightChunk000R : ℝ) := by
      norm_num [block237RightChunk001L, block237RightChunk000R]
    have hR : (block237RightChunk001R : ℝ) = (block237RightR : ℝ) := by
      norm_num [block237RightChunk001R, block237RightR]
    have hyc : y ∈ Icc (block237RightChunk001L : ℝ) (block237RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block237_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block237_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block237LeftL : ℝ) (block237LeftR : ℝ) →
    y ≠ 0 → y ≠ (block237S1 : ℝ) → y ≠ (block237S2 : ℝ) →
    y ≠ (block237S3 : ℝ) → y ≠ (block237S4 : ℝ) → 0 < block237V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block237RightL : ℝ) (block237RightR : ℝ) →
    y ≠ 0 → y ≠ (block237S1 : ℝ) → y ≠ (block237S2 : ℝ) →
    y ≠ (block237S3 : ℝ) → y ≠ (block237S4 : ℝ) → 0 < block237V y)

theorem block237_reallog_certificate_proof :
    block237_reallog_certificate := by
  exact ⟨block237_left_V_pos, block237_right_V_pos⟩

end Block237
end M1817475
end Erdos1038Lean
