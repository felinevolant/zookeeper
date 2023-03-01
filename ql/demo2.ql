/**
 * @id java/examples/testforexistcase
 * @name log detection
 * @description test for log detection and 看看既定的例子对不对
 * @problem.severity warning
 */

 import java

  //所有的IO语句
  class IOStmt extends Stmt{
    IOStmt(){
        exists(MethodAccess ma,Method m| 
            m.getDeclaringType().getAnAncestor*().hasQualifiedName("java.io", "File") or
            m.getDeclaringType().getAnAncestor*().hasQualifiedName("java.io", "InputStream") or
            m.getDeclaringType().getAnAncestor*().hasQualifiedName("java.io", "OutputStream") or
            m.getDeclaringType().getAnAncestor*().hasQualifiedName("java.io", "Reader") or
            m.getDeclaringType().getAnAncestor*().hasQualifiedName("java.io", "Writer") and
            ma.getMethod()=m and 
            this=ma.getEnclosingStmt())
    }
 }
 
 from IOStmt s
 select s,"this is the io stmt"
