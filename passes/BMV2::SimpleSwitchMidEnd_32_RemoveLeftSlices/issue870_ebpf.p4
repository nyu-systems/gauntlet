*** dumps/p4_16_samples/issue870_ebpf.p4/pruned/issue870_ebpf-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 16:59:30.396240400 +0200
--- dumps/p4_16_samples/issue870_ebpf.p4/pruned/issue870_ebpf-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 16:59:30.399969100 +0200
*************** control pipe(inout Headers_t headers, ou
*** 44,50 ****
      }
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
          pass = false;
!         headers.ipv4.srcAddr[31:0] = add[31:16] ++ add[15:0];
      }
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
--- 44,50 ----
      }
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
          pass = false;
!         headers.ipv4.srcAddr = headers.ipv4.srcAddr & ~32w0xffffffff | (bit<32>)(add[31:16] ++ add[15:0]) << 0 & 32w0xffffffff;
      }
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
