import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block261

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block261

open Set

def block261W1 : Rat := ((4481296249898133 : Rat) / 5000000000000000)
def block261W2 : Rat := ((3694540611307543 : Rat) / 50000000000000000)
def block261W3 : Rat := ((991777668448329 : Rat) / 5000000000000000)
def block261W4 : Rat := ((6088500946714353 : Rat) / 100000000000000000)
def block261S1 : Rat := ((18174751 : Rat) / 10000000)
def block261S2 : Rat := ((511587 : Rat) / 200000)
def block261S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block261S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block261V (y : ℝ) : ℝ :=
  ratPotential block261W1 block261W2 block261W3 block261W4 block261S1 block261S2 block261S3 block261S4 y

def block261LeftParamsCertificate : Bool :=
  allBoxesSameParams block261LeftBoxes block261W1 block261W2 block261W3 block261W4 block261S1 block261S2 block261S3 block261S4

theorem block261LeftParamsCertificate_eq_true :
    block261LeftParamsCertificate = true := by
  native_decide

theorem block261_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block261LeftL : ℝ) (block261LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block261S1 : ℝ))
    (hy2ne : y ≠ (block261S2 : ℝ))
    (hy3ne : y ≠ (block261S3 : ℝ))
    (hy4ne : y ≠ (block261S4 : ℝ)) :
    0 < block261V y := by
  have hcert := block261LeftCertificate_eq_true
  unfold block261LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block261LeftBoxes) (lo := block261LeftL) (hi := block261LeftR)
    (w1 := block261W1) (w2 := block261W2) (w3 := block261W3) (w4 := block261W4)
    (s1 := block261S1) (s2 := block261S2) (s3 := block261S3) (s4 := block261S4)
    hboxes hcover block261LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block261RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block261RightChunk000 block261W1 block261W2 block261W3 block261W4 block261S1 block261S2 block261S3 block261S4

theorem block261RightChunk000ParamsCertificate_eq_true :
    block261RightChunk000ParamsCertificate = true := by
  native_decide

theorem block261_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block261RightChunk000L : ℝ) (block261RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block261S1 : ℝ))
    (hy2ne : y ≠ (block261S2 : ℝ))
    (hy3ne : y ≠ (block261S3 : ℝ))
    (hy4ne : y ≠ (block261S4 : ℝ)) :
    0 < block261V y := by
  have hcert := block261RightChunk000Certificate_eq_true
  unfold block261RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block261RightChunk000) (lo := block261RightChunk000L) (hi := block261RightChunk000R)
    (w1 := block261W1) (w2 := block261W2) (w3 := block261W3) (w4 := block261W4)
    (s1 := block261S1) (s2 := block261S2) (s3 := block261S3) (s4 := block261S4)
    hboxes hcover block261RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block261RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block261RightChunk001 block261W1 block261W2 block261W3 block261W4 block261S1 block261S2 block261S3 block261S4

theorem block261RightChunk001ParamsCertificate_eq_true :
    block261RightChunk001ParamsCertificate = true := by
  native_decide

theorem block261_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block261RightChunk001L : ℝ) (block261RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block261S1 : ℝ))
    (hy2ne : y ≠ (block261S2 : ℝ))
    (hy3ne : y ≠ (block261S3 : ℝ))
    (hy4ne : y ≠ (block261S4 : ℝ)) :
    0 < block261V y := by
  have hcert := block261RightChunk001Certificate_eq_true
  unfold block261RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block261RightChunk001) (lo := block261RightChunk001L) (hi := block261RightChunk001R)
    (w1 := block261W1) (w2 := block261W2) (w3 := block261W3) (w4 := block261W4)
    (s1 := block261S1) (s2 := block261S2) (s3 := block261S3) (s4 := block261S4)
    hboxes hcover block261RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block261_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block261RightL : ℝ) (block261RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block261S1 : ℝ))
    (hy2ne : y ≠ (block261S2 : ℝ))
    (hy3ne : y ≠ (block261S3 : ℝ))
    (hy4ne : y ≠ (block261S4 : ℝ)) :
    0 < block261V y := by
  by_cases h0 : y ≤ (block261RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block261RightChunk000L : ℝ) (block261RightChunk000R : ℝ) := by
      have hL : (block261RightChunk000L : ℝ) = (block261RightL : ℝ) := by
        norm_num [block261RightChunk000L, block261RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block261_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block261RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block261RightChunk001L : ℝ) = (block261RightChunk000R : ℝ) := by
      norm_num [block261RightChunk001L, block261RightChunk000R]
    have hR : (block261RightChunk001R : ℝ) = (block261RightR : ℝ) := by
      norm_num [block261RightChunk001R, block261RightR]
    have hyc : y ∈ Icc (block261RightChunk001L : ℝ) (block261RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block261_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block261_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block261LeftL : ℝ) (block261LeftR : ℝ) →
    y ≠ 0 → y ≠ (block261S1 : ℝ) → y ≠ (block261S2 : ℝ) →
    y ≠ (block261S3 : ℝ) → y ≠ (block261S4 : ℝ) → 0 < block261V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block261RightL : ℝ) (block261RightR : ℝ) →
    y ≠ 0 → y ≠ (block261S1 : ℝ) → y ≠ (block261S2 : ℝ) →
    y ≠ (block261S3 : ℝ) → y ≠ (block261S4 : ℝ) → 0 < block261V y)

theorem block261_reallog_certificate_proof :
    block261_reallog_certificate := by
  exact ⟨block261_left_V_pos, block261_right_V_pos⟩

end Block261
end M1817475
end Erdos1038Lean
