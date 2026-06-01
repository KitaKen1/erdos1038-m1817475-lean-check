import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block196

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block196

open Set

def block196W1 : Rat := ((16822088520694507 : Rat) / 10000000000000000)
def block196W2 : Rat := (0 : Rat)
def block196W3 : Rat := ((448511241861063 : Rat) / 2500000000000000)
def block196W4 : Rat := ((1212198987226569 : Rat) / 12500000000000000)
def block196S1 : Rat := ((18174751 : Rat) / 10000000)
def block196S2 : Rat := ((511587 : Rat) / 200000)
def block196S3 : Rat := ((16982759665178571417 : Rat) / 6250000000000000000)
def block196S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block196V (y : ℝ) : ℝ :=
  ratPotential block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4 y

def block196LeftParamsCertificate : Bool :=
  allBoxesSameParams block196LeftBoxes block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196LeftParamsCertificate_eq_true :
    block196LeftParamsCertificate = true := by
  native_decide

theorem block196_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196LeftL : ℝ) (block196LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196LeftCertificate_eq_true
  unfold block196LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196LeftBoxes) (lo := block196LeftL) (hi := block196LeftR)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk000 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk000ParamsCertificate_eq_true :
    block196RightChunk000ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk000L : ℝ) (block196RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk000Certificate_eq_true
  unfold block196RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk000) (lo := block196RightChunk000L) (hi := block196RightChunk000R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk001 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk001ParamsCertificate_eq_true :
    block196RightChunk001ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk001L : ℝ) (block196RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk001Certificate_eq_true
  unfold block196RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk001) (lo := block196RightChunk001L) (hi := block196RightChunk001R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk002 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk002ParamsCertificate_eq_true :
    block196RightChunk002ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk002L : ℝ) (block196RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk002Certificate_eq_true
  unfold block196RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk002) (lo := block196RightChunk002L) (hi := block196RightChunk002R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk003 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk003ParamsCertificate_eq_true :
    block196RightChunk003ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk003L : ℝ) (block196RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk003Certificate_eq_true
  unfold block196RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk003) (lo := block196RightChunk003L) (hi := block196RightChunk003R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk004 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk004ParamsCertificate_eq_true :
    block196RightChunk004ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk004L : ℝ) (block196RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk004Certificate_eq_true
  unfold block196RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk004) (lo := block196RightChunk004L) (hi := block196RightChunk004R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk005 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk005ParamsCertificate_eq_true :
    block196RightChunk005ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk005L : ℝ) (block196RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk005Certificate_eq_true
  unfold block196RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk005) (lo := block196RightChunk005L) (hi := block196RightChunk005R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk006 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk006ParamsCertificate_eq_true :
    block196RightChunk006ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk006L : ℝ) (block196RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk006Certificate_eq_true
  unfold block196RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk006) (lo := block196RightChunk006L) (hi := block196RightChunk006R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk007ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk007 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk007ParamsCertificate_eq_true :
    block196RightChunk007ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk007_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk007L : ℝ) (block196RightChunk007R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk007Certificate_eq_true
  unfold block196RightChunk007Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk007) (lo := block196RightChunk007L) (hi := block196RightChunk007R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk007ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk008ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk008 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk008ParamsCertificate_eq_true :
    block196RightChunk008ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk008_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk008L : ℝ) (block196RightChunk008R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk008Certificate_eq_true
  unfold block196RightChunk008Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk008) (lo := block196RightChunk008L) (hi := block196RightChunk008R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk008ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk009ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk009 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk009ParamsCertificate_eq_true :
    block196RightChunk009ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk009_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk009L : ℝ) (block196RightChunk009R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk009Certificate_eq_true
  unfold block196RightChunk009Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk009) (lo := block196RightChunk009L) (hi := block196RightChunk009R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk009ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk010ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk010 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk010ParamsCertificate_eq_true :
    block196RightChunk010ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk010_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk010L : ℝ) (block196RightChunk010R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk010Certificate_eq_true
  unfold block196RightChunk010Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk010) (lo := block196RightChunk010L) (hi := block196RightChunk010R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk010ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk011ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk011 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk011ParamsCertificate_eq_true :
    block196RightChunk011ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk011_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk011L : ℝ) (block196RightChunk011R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk011Certificate_eq_true
  unfold block196RightChunk011Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk011) (lo := block196RightChunk011L) (hi := block196RightChunk011R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk011ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk012ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk012 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk012ParamsCertificate_eq_true :
    block196RightChunk012ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk012_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk012L : ℝ) (block196RightChunk012R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk012Certificate_eq_true
  unfold block196RightChunk012Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk012) (lo := block196RightChunk012L) (hi := block196RightChunk012R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk012ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk013ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk013 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk013ParamsCertificate_eq_true :
    block196RightChunk013ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk013_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk013L : ℝ) (block196RightChunk013R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk013Certificate_eq_true
  unfold block196RightChunk013Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk013) (lo := block196RightChunk013L) (hi := block196RightChunk013R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk013ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk014ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk014 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk014ParamsCertificate_eq_true :
    block196RightChunk014ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk014_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk014L : ℝ) (block196RightChunk014R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk014Certificate_eq_true
  unfold block196RightChunk014Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk014) (lo := block196RightChunk014L) (hi := block196RightChunk014R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk014ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk015ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk015 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk015ParamsCertificate_eq_true :
    block196RightChunk015ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk015_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk015L : ℝ) (block196RightChunk015R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk015Certificate_eq_true
  unfold block196RightChunk015Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk015) (lo := block196RightChunk015L) (hi := block196RightChunk015R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk015ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk016ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk016 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk016ParamsCertificate_eq_true :
    block196RightChunk016ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk016_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk016L : ℝ) (block196RightChunk016R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk016Certificate_eq_true
  unfold block196RightChunk016Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk016) (lo := block196RightChunk016L) (hi := block196RightChunk016R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk016ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk017ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk017 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk017ParamsCertificate_eq_true :
    block196RightChunk017ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk017_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk017L : ℝ) (block196RightChunk017R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk017Certificate_eq_true
  unfold block196RightChunk017Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk017) (lo := block196RightChunk017L) (hi := block196RightChunk017R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk017ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block196RightChunk018ParamsCertificate : Bool :=
  allBoxesSameParams block196RightChunk018 block196W1 block196W2 block196W3 block196W4 block196S1 block196S2 block196S3 block196S4

theorem block196RightChunk018ParamsCertificate_eq_true :
    block196RightChunk018ParamsCertificate = true := by
  native_decide

theorem block196_right_chunk018_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightChunk018L : ℝ) (block196RightChunk018R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  have hcert := block196RightChunk018Certificate_eq_true
  unfold block196RightChunk018Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block196RightChunk018) (lo := block196RightChunk018L) (hi := block196RightChunk018R)
    (w1 := block196W1) (w2 := block196W2) (w3 := block196W3) (w4 := block196W4)
    (s1 := block196S1) (s2 := block196S2) (s3 := block196S3) (s4 := block196S4)
    hboxes hcover block196RightChunk018ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block196_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block196RightL : ℝ) (block196RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block196S1 : ℝ))
    (hy2ne : y ≠ (block196S2 : ℝ))
    (hy3ne : y ≠ (block196S3 : ℝ))
    (hy4ne : y ≠ (block196S4 : ℝ)) :
    0 < block196V y := by
  by_cases h0 : y ≤ (block196RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block196RightChunk000L : ℝ) (block196RightChunk000R : ℝ) := by
      have hL : (block196RightChunk000L : ℝ) = (block196RightL : ℝ) := by
        norm_num [block196RightChunk000L, block196RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block196_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block196RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block196RightChunk001L : ℝ) (block196RightChunk001R : ℝ) := by
        have hprev : (block196RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block196RightChunk001L : ℝ) = (block196RightChunk000R : ℝ) := by
          norm_num [block196RightChunk001L, block196RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block196_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block196RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block196RightChunk002L : ℝ) (block196RightChunk002R : ℝ) := by
          have hprev : (block196RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block196RightChunk002L : ℝ) = (block196RightChunk001R : ℝ) := by
            norm_num [block196RightChunk002L, block196RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block196_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block196RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block196RightChunk003L : ℝ) (block196RightChunk003R : ℝ) := by
            have hprev : (block196RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block196RightChunk003L : ℝ) = (block196RightChunk002R : ℝ) := by
              norm_num [block196RightChunk003L, block196RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block196_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block196RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block196RightChunk004L : ℝ) (block196RightChunk004R : ℝ) := by
              have hprev : (block196RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block196RightChunk004L : ℝ) = (block196RightChunk003R : ℝ) := by
                norm_num [block196RightChunk004L, block196RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block196_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block196RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block196RightChunk005L : ℝ) (block196RightChunk005R : ℝ) := by
                have hprev : (block196RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block196RightChunk005L : ℝ) = (block196RightChunk004R : ℝ) := by
                  norm_num [block196RightChunk005L, block196RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block196_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              by_cases h6 : y ≤ (block196RightChunk006R : ℝ)
              · have hyc : y ∈ Icc (block196RightChunk006L : ℝ) (block196RightChunk006R : ℝ) := by
                  have hprev : (block196RightChunk005R : ℝ) < y := lt_of_not_ge h5
                  have hL : (block196RightChunk006L : ℝ) = (block196RightChunk005R : ℝ) := by
                    norm_num [block196RightChunk006L, block196RightChunk005R]
                  constructor
                  · linarith [hprev, hL]
                  · exact h6
                exact block196_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
              ·
                by_cases h7 : y ≤ (block196RightChunk007R : ℝ)
                · have hyc : y ∈ Icc (block196RightChunk007L : ℝ) (block196RightChunk007R : ℝ) := by
                    have hprev : (block196RightChunk006R : ℝ) < y := lt_of_not_ge h6
                    have hL : (block196RightChunk007L : ℝ) = (block196RightChunk006R : ℝ) := by
                      norm_num [block196RightChunk007L, block196RightChunk006R]
                    constructor
                    · linarith [hprev, hL]
                    · exact h7
                  exact block196_right_chunk007_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                ·
                  by_cases h8 : y ≤ (block196RightChunk008R : ℝ)
                  · have hyc : y ∈ Icc (block196RightChunk008L : ℝ) (block196RightChunk008R : ℝ) := by
                      have hprev : (block196RightChunk007R : ℝ) < y := lt_of_not_ge h7
                      have hL : (block196RightChunk008L : ℝ) = (block196RightChunk007R : ℝ) := by
                        norm_num [block196RightChunk008L, block196RightChunk007R]
                      constructor
                      · linarith [hprev, hL]
                      · exact h8
                    exact block196_right_chunk008_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                  ·
                    by_cases h9 : y ≤ (block196RightChunk009R : ℝ)
                    · have hyc : y ∈ Icc (block196RightChunk009L : ℝ) (block196RightChunk009R : ℝ) := by
                        have hprev : (block196RightChunk008R : ℝ) < y := lt_of_not_ge h8
                        have hL : (block196RightChunk009L : ℝ) = (block196RightChunk008R : ℝ) := by
                          norm_num [block196RightChunk009L, block196RightChunk008R]
                        constructor
                        · linarith [hprev, hL]
                        · exact h9
                      exact block196_right_chunk009_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                    ·
                      by_cases h10 : y ≤ (block196RightChunk010R : ℝ)
                      · have hyc : y ∈ Icc (block196RightChunk010L : ℝ) (block196RightChunk010R : ℝ) := by
                          have hprev : (block196RightChunk009R : ℝ) < y := lt_of_not_ge h9
                          have hL : (block196RightChunk010L : ℝ) = (block196RightChunk009R : ℝ) := by
                            norm_num [block196RightChunk010L, block196RightChunk009R]
                          constructor
                          · linarith [hprev, hL]
                          · exact h10
                        exact block196_right_chunk010_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                      ·
                        by_cases h11 : y ≤ (block196RightChunk011R : ℝ)
                        · have hyc : y ∈ Icc (block196RightChunk011L : ℝ) (block196RightChunk011R : ℝ) := by
                            have hprev : (block196RightChunk010R : ℝ) < y := lt_of_not_ge h10
                            have hL : (block196RightChunk011L : ℝ) = (block196RightChunk010R : ℝ) := by
                              norm_num [block196RightChunk011L, block196RightChunk010R]
                            constructor
                            · linarith [hprev, hL]
                            · exact h11
                          exact block196_right_chunk011_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                        ·
                          by_cases h12 : y ≤ (block196RightChunk012R : ℝ)
                          · have hyc : y ∈ Icc (block196RightChunk012L : ℝ) (block196RightChunk012R : ℝ) := by
                              have hprev : (block196RightChunk011R : ℝ) < y := lt_of_not_ge h11
                              have hL : (block196RightChunk012L : ℝ) = (block196RightChunk011R : ℝ) := by
                                norm_num [block196RightChunk012L, block196RightChunk011R]
                              constructor
                              · linarith [hprev, hL]
                              · exact h12
                            exact block196_right_chunk012_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                          ·
                            by_cases h13 : y ≤ (block196RightChunk013R : ℝ)
                            · have hyc : y ∈ Icc (block196RightChunk013L : ℝ) (block196RightChunk013R : ℝ) := by
                                have hprev : (block196RightChunk012R : ℝ) < y := lt_of_not_ge h12
                                have hL : (block196RightChunk013L : ℝ) = (block196RightChunk012R : ℝ) := by
                                  norm_num [block196RightChunk013L, block196RightChunk012R]
                                constructor
                                · linarith [hprev, hL]
                                · exact h13
                              exact block196_right_chunk013_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                            ·
                              by_cases h14 : y ≤ (block196RightChunk014R : ℝ)
                              · have hyc : y ∈ Icc (block196RightChunk014L : ℝ) (block196RightChunk014R : ℝ) := by
                                  have hprev : (block196RightChunk013R : ℝ) < y := lt_of_not_ge h13
                                  have hL : (block196RightChunk014L : ℝ) = (block196RightChunk013R : ℝ) := by
                                    norm_num [block196RightChunk014L, block196RightChunk013R]
                                  constructor
                                  · linarith [hprev, hL]
                                  · exact h14
                                exact block196_right_chunk014_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                              ·
                                by_cases h15 : y ≤ (block196RightChunk015R : ℝ)
                                · have hyc : y ∈ Icc (block196RightChunk015L : ℝ) (block196RightChunk015R : ℝ) := by
                                    have hprev : (block196RightChunk014R : ℝ) < y := lt_of_not_ge h14
                                    have hL : (block196RightChunk015L : ℝ) = (block196RightChunk014R : ℝ) := by
                                      norm_num [block196RightChunk015L, block196RightChunk014R]
                                    constructor
                                    · linarith [hprev, hL]
                                    · exact h15
                                  exact block196_right_chunk015_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                                ·
                                  by_cases h16 : y ≤ (block196RightChunk016R : ℝ)
                                  · have hyc : y ∈ Icc (block196RightChunk016L : ℝ) (block196RightChunk016R : ℝ) := by
                                      have hprev : (block196RightChunk015R : ℝ) < y := lt_of_not_ge h15
                                      have hL : (block196RightChunk016L : ℝ) = (block196RightChunk015R : ℝ) := by
                                        norm_num [block196RightChunk016L, block196RightChunk015R]
                                      constructor
                                      · linarith [hprev, hL]
                                      · exact h16
                                    exact block196_right_chunk016_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                                  ·
                                    by_cases h17 : y ≤ (block196RightChunk017R : ℝ)
                                    · have hyc : y ∈ Icc (block196RightChunk017L : ℝ) (block196RightChunk017R : ℝ) := by
                                        have hprev : (block196RightChunk016R : ℝ) < y := lt_of_not_ge h16
                                        have hL : (block196RightChunk017L : ℝ) = (block196RightChunk016R : ℝ) := by
                                          norm_num [block196RightChunk017L, block196RightChunk016R]
                                        constructor
                                        · linarith [hprev, hL]
                                        · exact h17
                                      exact block196_right_chunk017_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
                                    ·
                                      have hprev : (block196RightChunk017R : ℝ) < y := lt_of_not_ge h17
                                      have hL : (block196RightChunk018L : ℝ) = (block196RightChunk017R : ℝ) := by
                                        norm_num [block196RightChunk018L, block196RightChunk017R]
                                      have hR : (block196RightChunk018R : ℝ) = (block196RightR : ℝ) := by
                                        norm_num [block196RightChunk018R, block196RightR]
                                      have hyc : y ∈ Icc (block196RightChunk018L : ℝ) (block196RightChunk018R : ℝ) := by
                                        constructor
                                        · linarith [hprev, hL]
                                        · linarith [hy.2, hR]
                                      exact block196_right_chunk018_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block196_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block196LeftL : ℝ) (block196LeftR : ℝ) →
    y ≠ 0 → y ≠ (block196S1 : ℝ) → y ≠ (block196S2 : ℝ) →
    y ≠ (block196S3 : ℝ) → y ≠ (block196S4 : ℝ) → 0 < block196V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block196RightL : ℝ) (block196RightR : ℝ) →
    y ≠ 0 → y ≠ (block196S1 : ℝ) → y ≠ (block196S2 : ℝ) →
    y ≠ (block196S3 : ℝ) → y ≠ (block196S4 : ℝ) → 0 < block196V y)

theorem block196_reallog_certificate_proof :
    block196_reallog_certificate := by
  exact ⟨block196_left_V_pos, block196_right_V_pos⟩

end Block196
end M1817475
end Erdos1038Lean
