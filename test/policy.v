module policy(
	      input 	  clk,
	      input 	  rst,
	      input 	  invalid,
	      input [4:0] missId,
	      input [4:0] {erase(Valid newSpecValid,newSpecId; miss invalid, missId; newSpecId;H)} newSpecId,
	      input 	  {erase(Valid newSpecValid,newSpecId; miss invalid, missId; newSpecId;H)} newSpecValid,
	      output 	  {H} out
);


   reg 		    seq {erase(L;epol invalid;();H)} data_reg;
   reg 		    seq {erase(L;epol invalid;();H)} dreg_2;   

   
   always@(posedge clk) begin
      if (rst) data_reg <= 0;
      else data_reg <= data_reg; //should fail because policy may be true this cycle and become false next cycle
   end

   always@(posedge clk) begin
      if (rst || invalid) dreg_2 <= 0;
      else dreg_2 <= dreg_2; //should succeed because we don't copy if data was invalid
   end

   assign out = (invalid) ? data_reg : 0; //success, out is TOP

   reg       seq {erase(Valid vbit,spec;miss invalid, missId; spec;H)} vbit;   
   reg [4:0] seq {erase(Valid vbit,spec;miss invalid, missId; spec;H)} spec;

   wire      com {erase(Valid vbit,spec; miss invalid, missId; spec;H)} inv = (invalid && missId <= spec) || !vbit ? 1 : 0; 
   wire      com {erase(Valid newSpecValid,newSpecId; miss invalid,missId; newSpecId;H)} newvalid = (invalid && missId <= newSpecId) ? 0 : newSpecValid;
   
   wire      com {erase(Valid newSpecValid,newSpecId; miss invalid,missId; newSpecId;H) meet erase(Valid vbit,spec; miss invalid, missId; spec;H)} newLeqOld = (declassify(!vbit || (newSpecId <= spec), 
                  erase(Valid newSpecValid,newSpecId; miss invalid,missId; newSpecId;H) meet erase(Valid vbit,spec; miss invalid, missId; spec;H))) ? 1 : 0;
   
   
   always@(posedge clk) begin
      if (rst) begin
	 spec <= 0; //success, resetting to known values should always be OK
         vbit <= 0;
      end
      else if (newLeqOld) begin
	 vbit <= newvalid;	 
	 spec <= (newvalid) ? newSpecId : spec;	 
      end
      else if (inv) begin
//	 vbit <= 0;    //should succeed since this resets it to a HIGH label for next cycle
	 vbit <= newvalid;	
       	 spec <= (newvalid) ? newSpecId : spec;
      end
      else begin
	 spec <= spec; //should succeed since we've proven it not invalid
	 vbit <= vbit;
      end
   end
endmodule
