package io.kaitai.struct

import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.datatype.{BigEndian, DataType, FixedEndian, LittleEndian}
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.exprlang.Ast.boolop.{And, Or}
import io.kaitai.struct.exprlang.Ast.cmpop
import io.kaitai.struct.format._
import io.kaitai.struct.languages.components.{LanguageCompiler, LanguageCompilerStatic}
import io.kaitai.struct.precompile.CalculateSeqSizes
import io.kaitai.struct.translators.TypeDetector

import scala.collection.mutable.ListBuffer


class ElmClassCompiler(classSpecs: ClassSpecs, topClass: ClassSpec)
  extends AbstractCompiler {

  import ElmClassCompiler._

  val importList = new ImportList
  val provider = new ClassTypeProvider(classSpecs, topClass)

  val typeDetector = new TypeDetector(provider)

  val out = new StringLanguageOutputWriter(indent)

  def outFileName(topClass: ClassSpec): String = s"${type2name(topClass.nameAsStr)}.elm"

  def indent: String = "    "

  var decodeAndMapUsed = false
  var exposing: Set[String] = Set.empty

  override def compile: CompileLog.SpecSuccess = {
    compileClass(topClass)

    val write = new StringLanguageOutputWriter(indent)
    write.puts(
      s"""module ${type2name(topClass.name.last)} exposing (${exposing.mkString(", ")})
         |{-| $headerComment
         |-}
         |
         |import Bytes.Decode as D
         |import Bytes.Encode as E
         |
         |""".stripMargin)
    write.add(out)
    if (decodeAndMapUsed) {
      write.puts(
        s"""
           |andMap : Decoder a -> Decoder (a -> b) -> Decoder b
           |andMap argument function =
           |    D.map2 (<|) function argument
           |"""
          .stripMargin
      )
    } else {
      write.puts
    }
    write.puts("--- End of file")
    write.puts

    CompileLog.SpecSuccess("", List(CompileLog.FileSuccess(outFileName(topClass), write.result)))
  }

  def compileClass(curClass: ClassSpec): Unit = {
    provider.nowClass = curClass

    // Instances
    curClass.instances.foreach { case (id, instSpec) =>
      instSpec match {
        case pis: ParseInstanceSpec =>
          compileParseInstance(curClass, pis)
        case vis: ValueInstanceSpec =>
          compileValueInstance(id, vis)
      }
    }

    // Sequence
    compileRecords(curClass)


    // Enums
    curClass.enums.foreach { case (enumName, enumColl) => compileEnum(enumName, enumColl) }

    // Recursive types
    curClass.types.foreach { case (_, intClass) => compileClass(intClass) }

  }

  def compileRecords(curClass: ClassSpec): Unit = {
    val name = type2name(curClass.name.last)
    //    val endian = curClass.meta.endian
    //    LittleEndian
    //    BigEndian
    var fields = new ListBuffer[String]()
    var decoders = ""
    var encoders = new ListBuffer[String]()

    exposing ++= Set(type2name(name), s"decode${name}", s"encode${name}")
    val fieldsCount = curClass.seq.length

    CalculateSeqSizes.forEachSeqAttr(curClass, (attr, seqPos, sizeElement, sizeContainer) => {
      fields += compileRecordField(curClass, attr, seqPos, sizeElement, sizeContainer)
      encoders += compileRecordEncoder(EncodeElmSerializer.recordArgName, curClass, attr, seqPos, sizeElement, sizeContainer)
      decoders += compileRecordDecoder(fieldsCount, curClass, attr, seqPos, sizeElement, sizeContainer)
    })

    curClass.doc.summary.foreach(summary =>
      out.puts(s"{-| $summary\n-}")
    )

    val decodeFn = if (fieldsCount < 6 && fieldsCount > 1) {
      s"map${fieldsCount}"
    } else {
      s"map"
    }

    out.puts(
      s"""type alias ${name} =
         |    { ${fields.mkString("\n    , ")}
         |    }
         |
         |
         |${DecodeElmSerializer.prefix}${name} : ${DecodeElmSerializer.moduleName}.Decoder ${name}
         |${DecodeElmSerializer.prefix}${name} =
         |    ${DecodeElmSerializer.moduleName}.$decodeFn ${name}"""
        .stripMargin
    )
    out.putsLines(out.indentNow, decoders)
    out.puts(
      s"""
         |${EncodeElmSerializer.prefix}${name} : ${name} -> ${EncodeElmSerializer.moduleName}.Encoder
         |${EncodeElmSerializer.prefix}${name} ${EncodeElmSerializer.recordArgName} =
         |    ${EncodeElmSerializer.moduleName}.sequence
         |        [ ${encoders.mkString(s"\n${indent * 2}, ")}
         |        ]
      """.stripMargin)
  }

  def compileRecordField(classSpec: ClassSpec, attr: AttrSpec, seqPos: Option[Int], sizeElement: Sized, sizeContainer: Sized): String = {
    s"${type2field(attr.id.humanReadable)} : ${if (attr.isArray) "List " else ""}${kaitaiType2ElmType(attr.dataType)}"
  }

  def compileRecordEncoder(argName: String, classSpec: ClassSpec, attr: AttrSpec, seqPos: Option[Int], sizeElement: Sized, sizeContainer: Sized): String = {
    val (prefix, suffix) =
      if (attr.isArray) {
        (s"List.map ", s" |> ${EncodeElmSerializer.moduleName}.sequence")
      } else {
        ("", "")
      }

    s"$prefix${kaitaiType2ElmFunction(EncodeElmSerializer, attr.dataType)} $argName.${type2field(attr.id.humanReadable)}$suffix"
  }

  def compileRecordDecoder(fieldsCount: Int, curClass: ClassSpec, attr: AttrSpec, seqPos: Option[Int], sizeElement: Sized, sizeContainer: Sized): String = {
    // TODO find better way for prefix
    val prefix = (indent * 2) +
      (if (fieldsCount < 6) {
        ""
      } else {
        decodeAndMapUsed = true
        s"|> andMap "
      })
    val decoder = kaitaiType2ElmFunction(DecodeElmSerializer, attr.dataType, wrap = true)
    s"$prefix${compileDecoderRepeat(attr, seqPos, decoder)}"
  }

  def compileDecoderRepeat(attr: AttrSpec, seqPos: Option[Int], decoder: String): String = {
    seqPos.fold(s"${DecodeElmSerializer.moduleName}.fail") { pos =>
      val out = new StringLanguageOutputWriter(indent)
      attr.cond.repeat match {
        case NoRepeat => out.puts(decoder)
        case RepeatExpr(expr) => out.puts(s"$decoder -- (RepeatExpr ($expr))")
        case RepeatUntil(expr) =>
          out.puts
          // TODO fixme
          // From Top Level Start
          out.inc
          out.inc
          // From Top Level End

          out.inc
          out.puts(s"(${DecodeElmSerializer.moduleName}.loop (0, [])")
          out.inc
          out.puts("(\\(decodedBytes_, state_) ->")
          out.inc
          out.puts(s"if ${compileDecoderRepeatExpr(expr)} then")
          out.inc
          out.puts(s"${DecodeElmSerializer.moduleName}.Done decodedBytes_")
          out.dec
          out.puts
          out.puts("else")
          out.inc
          out.puts(s"${DecodeElmSerializer.moduleName}.andThen (\\chunk_ -> ${DecodeElmSerializer.moduleName}.loop (decodedBytes_ + findDecodeAmount, chunk_ :: state_)) $decoder")
          out.dec
          out.dec
          out.puts(s")")
          out.dec
          out.puts(s")")
          out.dec
          out.puts(s"-- END")
          //          out.puts(s"(\\chunk_ -> ")

          //          //          type2field
          //          out.puts(s"if type_ then")
          //          out.puts(s"--$expr")

          //          out.puts(s" state_ |> ${DecodeElmSerializer.moduleName}.Done")

          //          out.puts(s"else")

          //          out.puts(s"state_ |> Tuple.mapFirst ((::) chunk_) |> ${DecodeElmSerializer.moduleName}.Loop ")

          //          out.puts(s")")
          //          out.puts(s"|> List.reverse")
          out.puts(s"-- $expr")
        case RepeatEos => out.puts(s"$decoder -- (RepeatEos)")
      }
      out.result
    }
  }

  def compileDecoderRepeatExpr(expr: Ast.expr): String = {
    expr match {
      case Ast.expr.BoolOp(And, values: Seq[expr]) =>
        values.foldLeft("(&&)")((acc, a) => s"$acc (${translateExpr(a)})")
      case Ast.expr.BoolOp(Or, values: Seq[expr]) =>
        values.foldLeft("(||)")((acc, a) => s"$acc (${translateExpr(a)})")
    }
  }

  def translateExpr(expr: Ast.expr): String = {
    def opsToString(ops: cmpop): String = {
      ops match {
        case Ast.cmpop.Eq => "=="
        case Ast.cmpop.NotEq => "/="
        case Ast.cmpop.Lt => "<"
        case Ast.cmpop.LtE => ">="
        case Ast.cmpop.Gt => ">"
        case Ast.cmpop.GtE => ">="
      }
    }

    expr match {
      case Ast.expr.Compare(left, ops: cmpop, right) =>
        s"${translateExpr(left)} ${opsToString(ops)} ${translateExpr(right)}"
      case Ast.expr.Attribute(value, attr) => s"${'"'}Attribute(${value}, $attr)${'"'}"

//        typeDetector



      case Ast.expr.Str(s) => s"${'"'}$s${'"'}"
    }
  }


  //  Attribute(Name(identifier(_)),identifier(type)),
  //  Eq,
  //  Str(IEND)


  def compileParseInstance(classSpec: ClassSpec, inst: ParseInstanceSpec): Unit = {
    out.puts(s"<p><b>Parse instance</b>: ${inst.id.humanReadable}</p>")
    out.puts("<table class=\"table\">")
    out.puts("<tr>")
    out.puts(s"<td>expression(inst.pos)</td>")
    out.puts(s"<td>...</td>")
    out.puts(s"<td>${inst.id.humanReadable}</td>")
    out.puts(s"<td>${kaitaiType2ElmType(inst.dataType)}</td>")
    out.puts(s"<td>${inst.doc.summary.getOrElse("")}</td>")
    out.puts("</tr>")
    out.puts("</table>")
  }

  def compileValueInstance(id: InstanceIdentifier, vis: ValueInstanceSpec): Unit = {
    out.puts(s"FIXME---compileValueInstance---$id ${vis} ")
  }

  def compileEnum(enumName: String, enumColl: EnumSpec): Unit = {
    //    val out = new StringLanguageOutputWriter(indent)
    val name = type2name(enumName)
    out.puts(s"type $name")
    out.puts(s"$indent= ${enumColl.sortedSeq.map { case (id, value) => s"${type2name(value.name)} -- $id" }.mkString(s"\n$indent| ")}")
    out.puts
    out.puts
    // Decoder
    out.puts(s"${DecodeElmSerializer.prefix}$name : ${DecodeElmSerializer.moduleName}.Decoder Int -> ${DecodeElmSerializer.moduleName}.Decoder $name")
    out.puts(s"${DecodeElmSerializer.prefix}$name = ")
    out.inc
    out.puts(s"${DecodeElmSerializer.moduleName}.andThen")
    out.inc
    out.puts(s"(\\a ->")
    out.inc
    out.puts(s"case a of")
    out.inc
    enumColl.sortedSeq.foreach {
      case (id, value) =>
        out.puts(s"$id ->")
        out.inc
        out.puts(s"${DecodeElmSerializer.moduleName}.succeed ${type2name(value.name)}")
        out.dec
        out.puts
    }
    out.puts("_ ->")
    out.inc
    out.puts(s"${DecodeElmSerializer.moduleName}.fail")
    out.dec
    out.dec
    out.dec
    out.puts(s")")
    out.dec
    out.dec
    out.puts
    out.puts
    // Encoder
    //    case EnumType(name, basedOn) =>
    //    s"${dataTypeName(basedOn)}→${type2display(name)}"
    out.puts(s"${EncodeElmSerializer.prefix}$name : (Int -> ${EncodeElmSerializer.moduleName}.Encoder) -> $name -> ${EncodeElmSerializer.moduleName}.Encoder")
    out.puts(s"${EncodeElmSerializer.prefix}$name ${EncodeElmSerializer.encodeArgName} ${EncodeElmSerializer.recordArgName} = ")
    out.inc
    out.puts(s"${EncodeElmSerializer.encodeArgName}")
    out.inc
    out.puts(s"(case ${EncodeElmSerializer.recordArgName} of")
    out.inc
    enumColl.sortedSeq.foreach { case (id, value) =>
      out.puts(s"${type2name(value.name)} ->")
      out.inc
      out.puts(s"$id")
      out.dec
      if (enumColl.sortedSeq.last != (id, value)) out.puts
    }
    out.dec
    out.puts(s")")
    out.dec
    //    out.inc
    //    out.puts(s"|> ${EncodeElmSerializer.moduleName}.$unitType")
    //    out.dec
    out.dec
  }
}

object ElmClassCompiler extends LanguageCompilerStatic {
  // FIXME: Unused, should be probably separated from LanguageCompilerStatic
  override def getCompiler(
                            tp: ClassTypeProvider,
                            config: RuntimeConfig
                          ): LanguageCompiler = ???

  def headerComment = "This is a generated file! Please edit source .ksy file and use kaitai-struct-compiler to rebuild"

  def type2name(name: String): String = Utils.upperCamelCase(name)

  def type2field(name: String): String = if (name == "type") "type_" else Utils.lowerCamelCase(name)


  def enumSpec2Anchor(spec: EnumSpec): String = "enum-" + spec.name.mkString("-")

  def kaitaiType2ElmType(attrType: DataType): String = attrType match {
    case _: BytesEosType => "BytesEosType-FIXME"
    //      SwitchType
    case Int1Type(false) => "Int"
    case IntMultiType(false, Width2, endian) => "Int"
    case IntMultiType(false, Width4, endian) => "Int"
    case IntMultiType(false, Width8, endian) => "Int"

    case Int1Type(true) => "Int"
    case IntMultiType(true, Width2, endian) => "Int"
    case IntMultiType(true, Width4, endian) => "Int"
    case IntMultiType(true, Width8, endian) => "Int"

    case FloatMultiType(Width4, endian) => "Float"
    case FloatMultiType(Width8, endian) => "Float"

    case BitsType(width, bitEndian) => s"uint64_${bitEndian.toSuffix}"

    case _: BooleanType => "Bool"
    case CalcIntType => "Int"
    case CalcFloatType => "Float"

    case _: StrType => "String"
    case _: BytesType => "Bytes"

    case AnyType => "a" // interface{}

    /*--------------------------------------------------------------------------------------------------------------*/
    /* Work in progress */
    /*--------------------------------------------------------------------------------------------------------------*/

    case KaitaiStreamType | OwnedKaitaiStreamType => "KaitaiStreamType_OwnedKaitaiStreamType-FIXME"
    case KaitaiStructType | CalcKaitaiStructType => "KaitaiStreamType_CalcKaitaiStructType-FIXME"

    case ut: CalcUserTypeFromBytes => "CalcUserTypeFromBytes" + type2name(ut.name.last)
    case ut: CalcUserType => "CalcUserType" + type2name(ut.name.last)
    case ut: UserType => type2name(ut.name.last)

    case EnumType(name, basedOn) => type2name(name.last)
    //    case t: EnumType =>  // "EnumType" + types2class(t.enumSpec.get.name)

    case at: ArrayType => s"Array(${at})--FIXME"

    case st: SwitchType => s"SwitchType($st)--FIXME"
  }

  def endian2String(endian: Option[FixedEndian], defEndian: Option[FixedEndian] = None): String =
    endian.orElse(defEndian) match {
      case Some(LittleEndian) => "LE"
      case Some(BigEndian) => "BE"
      case None => ""
    }

  def wrapName(elmSerializer: ElmSerializer, attr: String, wrap: Boolean): String = {
    if (wrap) {
      s"(${elmSerializer.moduleName}.$attr)"
    } else {
      s"${elmSerializer.moduleName}.$attr"
    }
  }

  abstract sealed class ElmSerializer {
    def moduleName: String

    def prefix: String
  }

  case object DecodeElmSerializer extends ElmSerializer {
    override def moduleName: String = "D"

    override def prefix: String = "decode"
  }

  case object EncodeElmSerializer extends ElmSerializer {
    override def moduleName: String = "E"

    override def prefix: String = "encode"

    def recordArgName: String = "record_"

    def encodeArgName: String = "encoder_"
  }

  def kaitaiType2ElmFunction(elmSerializer: ElmSerializer, attrType: DataType, wrap: Boolean = false): String = {
    def localWrapName(attr: String, wrap: Boolean) = wrapName(elmSerializer, attr, wrap)

    attrType match {
      case Int1Type(false) => localWrapName("unsignedInt8", false)
      case IntMultiType(false, Width2, endian) => localWrapName(s"unsignedInt16 ${endian2String(endian)}", wrap)
      case IntMultiType(false, Width4, endian) => localWrapName(s"unsignedInt32 ${endian2String(endian)}", wrap)
      case IntMultiType(false, Width8, endian) => localWrapName(s"unsignedInt64 ${endian2String(endian)}", wrap)

      case Int1Type(true) => localWrapName("signedInt8", false)
      case IntMultiType(true, Width2, endian) => localWrapName(s"signedInt16 ${endian2String(endian)}", wrap)
      case IntMultiType(true, Width4, endian) => localWrapName(s"signedInt32 ${endian2String(endian)}", wrap)
      case IntMultiType(true, Width8, endian) => localWrapName(s"signedInt64 ${endian2String(endian)}", wrap)

      case FloatMultiType(Width4, endian) => localWrapName(s"float32 ${endian2String(endian)})", wrap)
      case FloatMultiType(Width8, endian) => localWrapName(s"float64 ${endian2String(endian)})", wrap)

      // Records
      case ut: UserType => s"${elmSerializer.prefix}${type2name(ut.name.last)}"

      // Custom Type
      case EnumType(name, basedOn) =>
        List(
          s"${if (wrap) "(" else ""}${elmSerializer.prefix}${type2name(name.last)} ",
          basedOn match {
            case Int1Type(false) => localWrapName("unsignedInt8", false)
            case IntMultiType(false, Width2, endian) => localWrapName(s"unsignedInt16 ${endian2String(endian)}", wrap)
            case IntMultiType(false, Width4, endian) => localWrapName(s"unsignedInt32 ${endian2String(endian)}", wrap)
            case IntMultiType(false, Width8, endian) => localWrapName(s"unsignedInt64 ${endian2String(endian)}", wrap)
            case Int1Type(true) => localWrapName("signedInt8", false)
            case IntMultiType(true, Width2, endian) => localWrapName(s"signedInt16 ${endian2String(endian)}", wrap)
            case IntMultiType(true, Width4, endian) => localWrapName(s"signedInt32 ${endian2String(endian)}", wrap)
            case IntMultiType(true, Width8, endian) => localWrapName(s"signedInt64 ${endian2String(endian)}", wrap)
          },
          if (wrap) ")" else ""
        ).mkString("")



      /*--------------------------------------------------------------------------------------------------------------*/
      /* Work in progress */
      /*--------------------------------------------------------------------------------------------------------------*/

      // String
      case StrFromBytesType(bytes: BytesType, encoding: String) =>
        elmSerializer match {
          case EncodeElmSerializer => strFromBytesTypeEncode(bytes, encoding, wrap)
          case DecodeElmSerializer => strFromBytesTypeDecode(bytes, encoding, wrap)
        }
      case _: StrType => localWrapName(s"StrType-FIXME", false)

      // BITS
      case BitsType(width, bitEndian) => localWrapName(s"BitsType${bitEndian.toSuffix}-FIXME", wrap)

      case _: BooleanType => localWrapName(s"bool-FIXME", false)
      case CalcIntType => localWrapName(s"int.CalcIntType-FIXME", false)
      case CalcFloatType => localWrapName(s"float64.CalcFloatType-FIXME", false)


      // Bytes
      case _: BytesEosType => localWrapName(s"BytesEosType-FIXME", false)
      case BytesLimitType(size, terminator, include, padRight, process) =>
        size match {
          case Ast.expr.IntNum(i) => localWrapName(s"bytes${if (elmSerializer == DecodeElmSerializer) s" $i" else ""}", elmSerializer == DecodeElmSerializer || wrap)
          case _ => localWrapName(s"BytesLimitType-size($size)-FIXME", false)
        }

      case _: BytesTerminatedType => localWrapName(s"BytesTerminatedType-FIXME", false)
      case _: BytesType => localWrapName(s"BytesType-FIXME", false)

      // Weird stuff
      case AnyType => "INTERFACE{}-FIXME"
      case KaitaiStreamType | OwnedKaitaiStreamType => localWrapName(s"OwnedKaitaiStreamType-FIXME", false)
      case KaitaiStructType | CalcKaitaiStructType => localWrapName(s"CalcKaitaiStructType-FIXME", false)
      case at: ArrayType => localWrapName(s"ArrayType-FIXME", false)
      case st: SwitchType => localWrapName(s"SwitchType-FIXME", false)
    }
  }

  def strFromBytesTypeEncode(bytes: BytesType, encoding: String, wrap: Boolean): String = {
    def localWrapName(attr: String, wrap: Boolean) = wrapName(EncodeElmSerializer, attr, wrap)

    bytes match {
      case BytesLimitType(size, terminator, include, padRight, process) =>
        size match {
          case Ast.expr.IntNum(i) => localWrapName(s"string", wrap)
          case _ => localWrapName(s"strFromBytesTypeEncode::BytesLimitType-size($size)-FIXME", false)
        }
      //BytesTerminatedType(0,false,true,true,None)
      case BytesTerminatedType(terminator, include, consume, eosError, process) =>
        s"${EncodeElmSerializer.moduleName}.sequence [${EncodeElmSerializer.moduleName}.string, ${EncodeElmSerializer.moduleName}.string]"
      //BytesEosType(None,false,None,None)
      case BytesEosType(terminator, include, padRight, process) =>
        "StrFromBytesType::BytesEosType()-FIXME"
      case _ => s"strFromBytesTypeEncode($bytes)-FIXME"
    }
  }

  def strFromBytesTypeDecode(bytes: BytesType, encoding: String, wrap: Boolean): String = {
    def localWrapName(attr: String, wrap: Boolean) = wrapName(DecodeElmSerializer, attr, wrap)

    bytes match {
      case BytesLimitType(size, terminator, include, padRight, process) =>
        size match {
          case Ast.expr.IntNum(i) => localWrapName(s"string $i", true)
          case _ => localWrapName(s"strFromBytesTypeDecode::BytesLimitType-size($size)-FIXME", false)
        }
      //BytesTerminatedType(0,false,true,true,None)
      case BytesTerminatedType(terminator, include, consume, eosError, process) => "strFromBytesTypeDecode::BytesTerminatedType()-FIXME"
      //BytesEosType(None,false,None,None)
      case BytesEosType(terminator, include, padRight, process) => "strFromBytesTypeDecode::BytesEosType()-FIXME"
      case _ => s"strFromBytesTypeDecode($bytes)-FIXME"
    }
  }
}
