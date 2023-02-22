/**
 * @id java/examples/detect-log
 * @name log detection
 * @description test for log detection
 * @problem.severity warning
 * @kind path-problem
 */

import java
import semmle.code.java.ControlFlowGraph
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.FlowSources
import DataFlow::PathGraph

//判断是否是日志调用的谓词
predicate isLogger(MethodAccess call) {
    exists(Method method|call.getMethod() = method and
    method.getDeclaringType().hasQualifiedName("org.slf4j", "Logger") and 
    not method.getName().matches("%Enabled"))
}

//isPLC用来储存日志前置代码
//predicate isPLC(Stmt plc) {

//}

//使用全局数据流分析

//数据流分析，用来完成数据依赖
class DataDepConfig extends DataFlow::Configuration {
    DataDepConfig() {
      this = "DataDependencies Configuration"
    }
  
    //数据源是数据依赖于sink的表达式
    override predicate isSource(DataFlow::Node source) {
      exists(Expr sink|
      source.asExpr() instanceof VarAccess 
      ) 
      //某个变量是数据依赖于sink
      
      //获取这个变量的表达式
      //这个是写好的一些漏洞规则，跟现在研究的关系不大
      //source instanceof RemoteFlowSource
    }
  
    //sink是所有日志调用方法里面的参数,变量参数不是string
    override predicate isSink(DataFlow::Node sink) {
      exists(MethodAccess call,Expr arg|
        //符合日志调用的条件
        isLogger(call) and
        //日志调用条件里面的参数，这个参数不是String类型的
        arg=call.getAnArgument() and
        not arg instanceof StringLiteral and
        //获取日志调用的表达式
        //call.getQualifier() = sink.asExpr()
        //这句话只能查到xxx.xxx()之前的东西，而且单个的参数也不能查 
        //arg.getAChildExpr()=sink.asExpr()
        //这句话可以查到xxx.xxx()之后的东西
        arg.getUnderlyingExpr()=sink.asExpr()
      )
    } 
  }

from DataFlow::PathNode src, DataFlow::PathNode sink,DataDepConfig config 
where config.hasFlowPath(src, sink) 
//select sink.getNode(),src, "flows to $@.", sink, "here",src.getNode()
select src.getNode(), src, sink, "source"
