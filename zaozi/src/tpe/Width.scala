package me.jiuyang.zaozi

object Width:
  def unknown: Width = -1.W

opaque type Width = Int

extension (w: Width) def toInt: Int = w.asInstanceOf[Int]

extension (x: Int)
  def W: Width =
    x match
      case x if x > 0   => x
      case x if x == 0  => x
      case x if x == -1 => x

extension (w: Width)
  def get:     Int     = w
  def unknown: Boolean = w == -1
