--- before_pass
+++ after_pass
@@ -1,6 +1,6 @@
 #include <core.p4>
 typedef bit<9> PortIdUInt_t;
-type bit<9> PortId_t;
+typedef bit<9> PortId_t;
 struct M {
     PortId_t     e;
     PortIdUInt_t es;
