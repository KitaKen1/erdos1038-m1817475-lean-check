import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block492

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block492

open Set

def block492W1 : Rat := ((48252556707267313 : Rat) / 100000000000000000)
def block492W2 : Rat := (0 : Rat)
def block492W3 : Rat := ((3996606023305999 : Rat) / 10000000000000000)
def block492W4 : Rat := ((29234993135681113 : Rat) / 1000000000000000000)
def block492S1 : Rat := ((18174751 : Rat) / 10000000)
def block492S2 : Rat := ((511587 : Rat) / 200000)
def block492S3 : Rat := ((130515396517857142999 : Rat) / 50000000000000000000)
def block492S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block492V (y : ℝ) : ℝ :=
  ratPotential block492W1 block492W2 block492W3 block492W4 block492S1 block492S2 block492S3 block492S4 y

def block492LeftParamsCertificate : Bool :=
  allBoxesSameParams block492LeftBoxes block492W1 block492W2 block492W3 block492W4 block492S1 block492S2 block492S3 block492S4

theorem block492LeftParamsCertificate_eq_true :
    block492LeftParamsCertificate = true := by
  native_decide

theorem block492_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block492LeftL : ℝ) (block492LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block492S1 : ℝ))
    (hy2ne : y ≠ (block492S2 : ℝ))
    (hy3ne : y ≠ (block492S3 : ℝ))
    (hy4ne : y ≠ (block492S4 : ℝ)) :
    0 < block492V y := by
  have hcert := block492LeftCertificate_eq_true
  unfold block492LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block492LeftBoxes) (lo := block492LeftL) (hi := block492LeftR)
    (w1 := block492W1) (w2 := block492W2) (w3 := block492W3) (w4 := block492W4)
    (s1 := block492S1) (s2 := block492S2) (s3 := block492S3) (s4 := block492S4)
    hboxes hcover block492LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block492RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block492RightChunk000 block492W1 block492W2 block492W3 block492W4 block492S1 block492S2 block492S3 block492S4

theorem block492RightChunk000ParamsCertificate_eq_true :
    block492RightChunk000ParamsCertificate = true := by
  native_decide

theorem block492_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block492RightChunk000L : ℝ) (block492RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block492S1 : ℝ))
    (hy2ne : y ≠ (block492S2 : ℝ))
    (hy3ne : y ≠ (block492S3 : ℝ))
    (hy4ne : y ≠ (block492S4 : ℝ)) :
    0 < block492V y := by
  have hcert := block492RightChunk000Certificate_eq_true
  unfold block492RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block492RightChunk000) (lo := block492RightChunk000L) (hi := block492RightChunk000R)
    (w1 := block492W1) (w2 := block492W2) (w3 := block492W3) (w4 := block492W4)
    (s1 := block492S1) (s2 := block492S2) (s3 := block492S3) (s4 := block492S4)
    hboxes hcover block492RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block492_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block492RightL : ℝ) (block492RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block492S1 : ℝ))
    (hy2ne : y ≠ (block492S2 : ℝ))
    (hy3ne : y ≠ (block492S3 : ℝ))
    (hy4ne : y ≠ (block492S4 : ℝ)) :
    0 < block492V y := by
  have hL : (block492RightChunk000L : ℝ) = (block492RightL : ℝ) := by
    norm_num [block492RightChunk000L, block492RightL]
  have hR : (block492RightChunk000R : ℝ) = (block492RightR : ℝ) := by
    norm_num [block492RightChunk000R, block492RightR]
  have hyc : y ∈ Icc (block492RightChunk000L : ℝ) (block492RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block492_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block492_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block492LeftL : ℝ) (block492LeftR : ℝ) →
    y ≠ 0 → y ≠ (block492S1 : ℝ) → y ≠ (block492S2 : ℝ) →
    y ≠ (block492S3 : ℝ) → y ≠ (block492S4 : ℝ) → 0 < block492V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block492RightL : ℝ) (block492RightR : ℝ) →
    y ≠ 0 → y ≠ (block492S1 : ℝ) → y ≠ (block492S2 : ℝ) →
    y ≠ (block492S3 : ℝ) → y ≠ (block492S4 : ℝ) → 0 < block492V y)

theorem block492_reallog_certificate_proof :
    block492_reallog_certificate := by
  exact ⟨block492_left_V_pos, block492_right_V_pos⟩

end Block492
end M1817475
end Erdos1038Lean
