import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block484

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block484

open Set

def block484W1 : Rat := ((201468701489243 : Rat) / 400000000000000)
def block484W2 : Rat := (0 : Rat)
def block484W3 : Rat := ((3852070239559497 : Rat) / 10000000000000000)
def block484W4 : Rat := ((4736612173262743 : Rat) / 125000000000000000)
def block484S1 : Rat := ((18174751 : Rat) / 10000000)
def block484S2 : Rat := ((511587 : Rat) / 200000)
def block484S3 : Rat := ((26134357875000000027 : Rat) / 10000000000000000000)
def block484S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block484V (y : ℝ) : ℝ :=
  ratPotential block484W1 block484W2 block484W3 block484W4 block484S1 block484S2 block484S3 block484S4 y

def block484LeftParamsCertificate : Bool :=
  allBoxesSameParams block484LeftBoxes block484W1 block484W2 block484W3 block484W4 block484S1 block484S2 block484S3 block484S4

theorem block484LeftParamsCertificate_eq_true :
    block484LeftParamsCertificate = true := by
  native_decide

theorem block484_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block484LeftL : ℝ) (block484LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block484S1 : ℝ))
    (hy2ne : y ≠ (block484S2 : ℝ))
    (hy3ne : y ≠ (block484S3 : ℝ))
    (hy4ne : y ≠ (block484S4 : ℝ)) :
    0 < block484V y := by
  have hcert := block484LeftCertificate_eq_true
  unfold block484LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block484LeftBoxes) (lo := block484LeftL) (hi := block484LeftR)
    (w1 := block484W1) (w2 := block484W2) (w3 := block484W3) (w4 := block484W4)
    (s1 := block484S1) (s2 := block484S2) (s3 := block484S3) (s4 := block484S4)
    hboxes hcover block484LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block484RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block484RightChunk000 block484W1 block484W2 block484W3 block484W4 block484S1 block484S2 block484S3 block484S4

theorem block484RightChunk000ParamsCertificate_eq_true :
    block484RightChunk000ParamsCertificate = true := by
  native_decide

theorem block484_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block484RightChunk000L : ℝ) (block484RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block484S1 : ℝ))
    (hy2ne : y ≠ (block484S2 : ℝ))
    (hy3ne : y ≠ (block484S3 : ℝ))
    (hy4ne : y ≠ (block484S4 : ℝ)) :
    0 < block484V y := by
  have hcert := block484RightChunk000Certificate_eq_true
  unfold block484RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block484RightChunk000) (lo := block484RightChunk000L) (hi := block484RightChunk000R)
    (w1 := block484W1) (w2 := block484W2) (w3 := block484W3) (w4 := block484W4)
    (s1 := block484S1) (s2 := block484S2) (s3 := block484S3) (s4 := block484S4)
    hboxes hcover block484RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block484_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block484RightL : ℝ) (block484RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block484S1 : ℝ))
    (hy2ne : y ≠ (block484S2 : ℝ))
    (hy3ne : y ≠ (block484S3 : ℝ))
    (hy4ne : y ≠ (block484S4 : ℝ)) :
    0 < block484V y := by
  have hL : (block484RightChunk000L : ℝ) = (block484RightL : ℝ) := by
    norm_num [block484RightChunk000L, block484RightL]
  have hR : (block484RightChunk000R : ℝ) = (block484RightR : ℝ) := by
    norm_num [block484RightChunk000R, block484RightR]
  have hyc : y ∈ Icc (block484RightChunk000L : ℝ) (block484RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block484_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block484_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block484LeftL : ℝ) (block484LeftR : ℝ) →
    y ≠ 0 → y ≠ (block484S1 : ℝ) → y ≠ (block484S2 : ℝ) →
    y ≠ (block484S3 : ℝ) → y ≠ (block484S4 : ℝ) → 0 < block484V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block484RightL : ℝ) (block484RightR : ℝ) →
    y ≠ 0 → y ≠ (block484S1 : ℝ) → y ≠ (block484S2 : ℝ) →
    y ≠ (block484S3 : ℝ) → y ≠ (block484S4 : ℝ) → 0 < block484V y)

theorem block484_reallog_certificate_proof :
    block484_reallog_certificate := by
  exact ⟨block484_left_V_pos, block484_right_V_pos⟩

end Block484
end M1817475
end Erdos1038Lean
