import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block186

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block186

open Set

def block186W1 : Rat := ((17661103135179 : Rat) / 10000000000000)
def block186W2 : Rat := (0 : Rat)
def block186W3 : Rat := ((1771063606594249 : Rat) / 10000000000000000)
def block186W4 : Rat := ((4726470658437517 : Rat) / 50000000000000000)
def block186S1 : Rat := ((18174751 : Rat) / 10000000)
def block186S2 : Rat := ((511587 : Rat) / 200000)
def block186S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block186S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block186V (y : ℝ) : ℝ :=
  ratPotential block186W1 block186W2 block186W3 block186W4 block186S1 block186S2 block186S3 block186S4 y

def block186LeftParamsCertificate : Bool :=
  allBoxesSameParams block186LeftBoxes block186W1 block186W2 block186W3 block186W4 block186S1 block186S2 block186S3 block186S4

theorem block186LeftParamsCertificate_eq_true :
    block186LeftParamsCertificate = true := by
  native_decide

theorem block186_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block186LeftL : ℝ) (block186LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block186S1 : ℝ))
    (hy2ne : y ≠ (block186S2 : ℝ))
    (hy3ne : y ≠ (block186S3 : ℝ))
    (hy4ne : y ≠ (block186S4 : ℝ)) :
    0 < block186V y := by
  have hcert := block186LeftCertificate_eq_true
  unfold block186LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block186LeftBoxes) (lo := block186LeftL) (hi := block186LeftR)
    (w1 := block186W1) (w2 := block186W2) (w3 := block186W3) (w4 := block186W4)
    (s1 := block186S1) (s2 := block186S2) (s3 := block186S3) (s4 := block186S4)
    hboxes hcover block186LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block186RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block186RightChunk000 block186W1 block186W2 block186W3 block186W4 block186S1 block186S2 block186S3 block186S4

theorem block186RightChunk000ParamsCertificate_eq_true :
    block186RightChunk000ParamsCertificate = true := by
  native_decide

theorem block186_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block186RightChunk000L : ℝ) (block186RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block186S1 : ℝ))
    (hy2ne : y ≠ (block186S2 : ℝ))
    (hy3ne : y ≠ (block186S3 : ℝ))
    (hy4ne : y ≠ (block186S4 : ℝ)) :
    0 < block186V y := by
  have hcert := block186RightChunk000Certificate_eq_true
  unfold block186RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block186RightChunk000) (lo := block186RightChunk000L) (hi := block186RightChunk000R)
    (w1 := block186W1) (w2 := block186W2) (w3 := block186W3) (w4 := block186W4)
    (s1 := block186S1) (s2 := block186S2) (s3 := block186S3) (s4 := block186S4)
    hboxes hcover block186RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block186RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block186RightChunk001 block186W1 block186W2 block186W3 block186W4 block186S1 block186S2 block186S3 block186S4

theorem block186RightChunk001ParamsCertificate_eq_true :
    block186RightChunk001ParamsCertificate = true := by
  native_decide

theorem block186_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block186RightChunk001L : ℝ) (block186RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block186S1 : ℝ))
    (hy2ne : y ≠ (block186S2 : ℝ))
    (hy3ne : y ≠ (block186S3 : ℝ))
    (hy4ne : y ≠ (block186S4 : ℝ)) :
    0 < block186V y := by
  have hcert := block186RightChunk001Certificate_eq_true
  unfold block186RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block186RightChunk001) (lo := block186RightChunk001L) (hi := block186RightChunk001R)
    (w1 := block186W1) (w2 := block186W2) (w3 := block186W3) (w4 := block186W4)
    (s1 := block186S1) (s2 := block186S2) (s3 := block186S3) (s4 := block186S4)
    hboxes hcover block186RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block186_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block186RightL : ℝ) (block186RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block186S1 : ℝ))
    (hy2ne : y ≠ (block186S2 : ℝ))
    (hy3ne : y ≠ (block186S3 : ℝ))
    (hy4ne : y ≠ (block186S4 : ℝ)) :
    0 < block186V y := by
  by_cases h0 : y ≤ (block186RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block186RightChunk000L : ℝ) (block186RightChunk000R : ℝ) := by
      have hL : (block186RightChunk000L : ℝ) = (block186RightL : ℝ) := by
        norm_num [block186RightChunk000L, block186RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block186_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block186RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block186RightChunk001L : ℝ) = (block186RightChunk000R : ℝ) := by
      norm_num [block186RightChunk001L, block186RightChunk000R]
    have hR : (block186RightChunk001R : ℝ) = (block186RightR : ℝ) := by
      norm_num [block186RightChunk001R, block186RightR]
    have hyc : y ∈ Icc (block186RightChunk001L : ℝ) (block186RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block186_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block186_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block186LeftL : ℝ) (block186LeftR : ℝ) →
    y ≠ 0 → y ≠ (block186S1 : ℝ) → y ≠ (block186S2 : ℝ) →
    y ≠ (block186S3 : ℝ) → y ≠ (block186S4 : ℝ) → 0 < block186V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block186RightL : ℝ) (block186RightR : ℝ) →
    y ≠ 0 → y ≠ (block186S1 : ℝ) → y ≠ (block186S2 : ℝ) →
    y ≠ (block186S3 : ℝ) → y ≠ (block186S4 : ℝ) → 0 < block186V y)

theorem block186_reallog_certificate_proof :
    block186_reallog_certificate := by
  exact ⟨block186_left_V_pos, block186_right_V_pos⟩

end Block186
end M1817475
end Erdos1038Lean
