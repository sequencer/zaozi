// SPDX-License-Identifier: Apache-2.0

package me.jiuyang.zaozi.internal

trait Named:
  def name:     String
  def nameKind: NameKind

enum NameKind:
  case Droppable, Interesting

def toMLIR(
  nk:        NameKind
) = nk match
  case NameKind.Droppable   => me.jiuyang.zaozi.circtlib.FIRRTLNameKind.DroppableName
  case NameKind.Interesting => me.jiuyang.zaozi.circtlib.FIRRTLNameKind.InterestingName
