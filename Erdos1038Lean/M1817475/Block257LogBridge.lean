import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block257

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block257

open Set

def block257W1 : Rat := ((4444306414744157 : Rat) / 5000000000000000)
def block257W2 : Rat := ((7613572355532329 : Rat) / 100000000000000000)
def block257W3 : Rat := ((19421940538691831 : Rat) / 100000000000000000)
def block257W4 : Rat := ((3182531645861657 : Rat) / 50000000000000000)
def block257S1 : Rat := ((18174751 : Rat) / 10000000)
def block257S2 : Rat := ((511587 : Rat) / 200000)
def block257S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block257S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block257V (y : ℝ) : ℝ :=
  ratPotential block257W1 block257W2 block257W3 block257W4 block257S1 block257S2 block257S3 block257S4 y

def block257LeftParamsCertificate : Bool :=
  allBoxesSameParams block257LeftBoxes block257W1 block257W2 block257W3 block257W4 block257S1 block257S2 block257S3 block257S4

theorem block257LeftParamsCertificate_eq_true :
    block257LeftParamsCertificate = true := by
  native_decide

theorem block257_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block257LeftL : ℝ) (block257LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block257S1 : ℝ))
    (hy2ne : y ≠ (block257S2 : ℝ))
    (hy3ne : y ≠ (block257S3 : ℝ))
    (hy4ne : y ≠ (block257S4 : ℝ)) :
    0 < block257V y := by
  have hcert := block257LeftCertificate_eq_true
  unfold block257LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block257LeftBoxes) (lo := block257LeftL) (hi := block257LeftR)
    (w1 := block257W1) (w2 := block257W2) (w3 := block257W3) (w4 := block257W4)
    (s1 := block257S1) (s2 := block257S2) (s3 := block257S3) (s4 := block257S4)
    hboxes hcover block257LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block257RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block257RightChunk000 block257W1 block257W2 block257W3 block257W4 block257S1 block257S2 block257S3 block257S4

theorem block257RightChunk000ParamsCertificate_eq_true :
    block257RightChunk000ParamsCertificate = true := by
  native_decide

theorem block257_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block257RightChunk000L : ℝ) (block257RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block257S1 : ℝ))
    (hy2ne : y ≠ (block257S2 : ℝ))
    (hy3ne : y ≠ (block257S3 : ℝ))
    (hy4ne : y ≠ (block257S4 : ℝ)) :
    0 < block257V y := by
  have hcert := block257RightChunk000Certificate_eq_true
  unfold block257RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block257RightChunk000) (lo := block257RightChunk000L) (hi := block257RightChunk000R)
    (w1 := block257W1) (w2 := block257W2) (w3 := block257W3) (w4 := block257W4)
    (s1 := block257S1) (s2 := block257S2) (s3 := block257S3) (s4 := block257S4)
    hboxes hcover block257RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block257RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block257RightChunk001 block257W1 block257W2 block257W3 block257W4 block257S1 block257S2 block257S3 block257S4

theorem block257RightChunk001ParamsCertificate_eq_true :
    block257RightChunk001ParamsCertificate = true := by
  native_decide

theorem block257_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block257RightChunk001L : ℝ) (block257RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block257S1 : ℝ))
    (hy2ne : y ≠ (block257S2 : ℝ))
    (hy3ne : y ≠ (block257S3 : ℝ))
    (hy4ne : y ≠ (block257S4 : ℝ)) :
    0 < block257V y := by
  have hcert := block257RightChunk001Certificate_eq_true
  unfold block257RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block257RightChunk001) (lo := block257RightChunk001L) (hi := block257RightChunk001R)
    (w1 := block257W1) (w2 := block257W2) (w3 := block257W3) (w4 := block257W4)
    (s1 := block257S1) (s2 := block257S2) (s3 := block257S3) (s4 := block257S4)
    hboxes hcover block257RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block257_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block257RightL : ℝ) (block257RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block257S1 : ℝ))
    (hy2ne : y ≠ (block257S2 : ℝ))
    (hy3ne : y ≠ (block257S3 : ℝ))
    (hy4ne : y ≠ (block257S4 : ℝ)) :
    0 < block257V y := by
  by_cases h0 : y ≤ (block257RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block257RightChunk000L : ℝ) (block257RightChunk000R : ℝ) := by
      have hL : (block257RightChunk000L : ℝ) = (block257RightL : ℝ) := by
        norm_num [block257RightChunk000L, block257RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block257_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block257RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block257RightChunk001L : ℝ) = (block257RightChunk000R : ℝ) := by
      norm_num [block257RightChunk001L, block257RightChunk000R]
    have hR : (block257RightChunk001R : ℝ) = (block257RightR : ℝ) := by
      norm_num [block257RightChunk001R, block257RightR]
    have hyc : y ∈ Icc (block257RightChunk001L : ℝ) (block257RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block257_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block257_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block257LeftL : ℝ) (block257LeftR : ℝ) →
    y ≠ 0 → y ≠ (block257S1 : ℝ) → y ≠ (block257S2 : ℝ) →
    y ≠ (block257S3 : ℝ) → y ≠ (block257S4 : ℝ) → 0 < block257V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block257RightL : ℝ) (block257RightR : ℝ) →
    y ≠ 0 → y ≠ (block257S1 : ℝ) → y ≠ (block257S2 : ℝ) →
    y ≠ (block257S3 : ℝ) → y ≠ (block257S4 : ℝ) → 0 < block257V y)

theorem block257_reallog_certificate_proof :
    block257_reallog_certificate := by
  exact ⟨block257_left_V_pos, block257_right_V_pos⟩

end Block257
end M1817475
end Erdos1038Lean
