import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block449

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block449

open Set

def block449W1 : Rat := ((1200458340865571 : Rat) / 2000000000000000)
def block449W2 : Rat := (0 : Rat)
def block449W3 : Rat := ((3317463944587981 : Rat) / 10000000000000000)
def block449W4 : Rat := ((6780793405623121 : Rat) / 100000000000000000)
def block449S1 : Rat := ((18174751 : Rat) / 10000000)
def block449S2 : Rat := ((511587 : Rat) / 200000)
def block449S3 : Rat := ((26271201625000000021 : Rat) / 10000000000000000000)
def block449S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block449V (y : ℝ) : ℝ :=
  ratPotential block449W1 block449W2 block449W3 block449W4 block449S1 block449S2 block449S3 block449S4 y

def block449LeftParamsCertificate : Bool :=
  allBoxesSameParams block449LeftBoxes block449W1 block449W2 block449W3 block449W4 block449S1 block449S2 block449S3 block449S4

theorem block449LeftParamsCertificate_eq_true :
    block449LeftParamsCertificate = true := by
  native_decide

theorem block449_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block449LeftL : ℝ) (block449LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block449S1 : ℝ))
    (hy2ne : y ≠ (block449S2 : ℝ))
    (hy3ne : y ≠ (block449S3 : ℝ))
    (hy4ne : y ≠ (block449S4 : ℝ)) :
    0 < block449V y := by
  have hcert := block449LeftCertificate_eq_true
  unfold block449LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block449LeftBoxes) (lo := block449LeftL) (hi := block449LeftR)
    (w1 := block449W1) (w2 := block449W2) (w3 := block449W3) (w4 := block449W4)
    (s1 := block449S1) (s2 := block449S2) (s3 := block449S3) (s4 := block449S4)
    hboxes hcover block449LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block449RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block449RightChunk000 block449W1 block449W2 block449W3 block449W4 block449S1 block449S2 block449S3 block449S4

theorem block449RightChunk000ParamsCertificate_eq_true :
    block449RightChunk000ParamsCertificate = true := by
  native_decide

theorem block449_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block449RightChunk000L : ℝ) (block449RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block449S1 : ℝ))
    (hy2ne : y ≠ (block449S2 : ℝ))
    (hy3ne : y ≠ (block449S3 : ℝ))
    (hy4ne : y ≠ (block449S4 : ℝ)) :
    0 < block449V y := by
  have hcert := block449RightChunk000Certificate_eq_true
  unfold block449RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block449RightChunk000) (lo := block449RightChunk000L) (hi := block449RightChunk000R)
    (w1 := block449W1) (w2 := block449W2) (w3 := block449W3) (w4 := block449W4)
    (s1 := block449S1) (s2 := block449S2) (s3 := block449S3) (s4 := block449S4)
    hboxes hcover block449RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block449_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block449RightL : ℝ) (block449RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block449S1 : ℝ))
    (hy2ne : y ≠ (block449S2 : ℝ))
    (hy3ne : y ≠ (block449S3 : ℝ))
    (hy4ne : y ≠ (block449S4 : ℝ)) :
    0 < block449V y := by
  have hL : (block449RightChunk000L : ℝ) = (block449RightL : ℝ) := by
    norm_num [block449RightChunk000L, block449RightL]
  have hR : (block449RightChunk000R : ℝ) = (block449RightR : ℝ) := by
    norm_num [block449RightChunk000R, block449RightR]
  have hyc : y ∈ Icc (block449RightChunk000L : ℝ) (block449RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block449_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block449_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block449LeftL : ℝ) (block449LeftR : ℝ) →
    y ≠ 0 → y ≠ (block449S1 : ℝ) → y ≠ (block449S2 : ℝ) →
    y ≠ (block449S3 : ℝ) → y ≠ (block449S4 : ℝ) → 0 < block449V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block449RightL : ℝ) (block449RightR : ℝ) →
    y ≠ 0 → y ≠ (block449S1 : ℝ) → y ≠ (block449S2 : ℝ) →
    y ≠ (block449S3 : ℝ) → y ≠ (block449S4 : ℝ) → 0 < block449V y)

theorem block449_reallog_certificate_proof :
    block449_reallog_certificate := by
  exact ⟨block449_left_V_pos, block449_right_V_pos⟩

end Block449
end M1817475
end Erdos1038Lean
