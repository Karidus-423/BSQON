#include "smt_extract.h"
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

// MOCK_RUNNER,
// TEST_RUNNER,
typedef enum _ExtractorMode{
	MOCK_RUNNER,
	TEST_RUNNER,
}ExtractorMode;

// Mock Name, target_type_info 
//
// std::pmr::unordered_map<std::string, std::string> mock_signatures;
// std::vector<std::string> bsq_files;
// std::string smt_file;
// std::string type_info;
// ExtractorMode mode;
typedef struct _ExtractorMetadata
{
	std::vector<std::string> bsq_files;
	std::pmr::unordered_map<std::string, std::string> mock_signatures;
	std::string smt_file;
	std::string type_info;
	ExtractorMode mode;
} ExtractorMetadata;

char* readFile(const char* filename)
{
    FILE* f = fopen(filename, "r");
    if (!f)
    {
        perror("fopen");
    }
    fseek(f, 0, SEEK_END);
    long length = ftell(f);
    rewind(f);
    char* bfr = (char*)malloc(sizeof(char) * length);

    fread(bfr, sizeof(char), length, f);

    fclose(f);
    return bfr;
}

std::optional<z3::expr> findConstantInModel(z3::model m, std::string id)
{
    uint n_consts = m.num_consts();
    for (uint i = 0; i < n_consts; ++i)
    {
        z3::func_decl fn_const = m.get_const_decl(i);
        std::string fn_id = fn_const.name().str();

        if (fn_id == id)
        {
            return fn_const();
        }
    }

    return std::nullopt;
}


std::string getSolverFromSMTFormula(std::string smt_file)
{
    if (validPath(smt_file.c_str(), "smt2") == false)
    {
        badArgs("Incorrect .smt2 file");
    }
    char* smt_bfr = readFile(smt_file.c_str());
    std::string smt_str(smt_bfr);
    free(smt_bfr);

    // HACK: Fix to prevent z3 to optimize the functions that use define-fun.
    std::string helper_fn = ";;;;;;;;;;;;;;;\n (declare-fun MockTest (Int) Int) "
                            "(assert (> (MockTest 5) 2))";
    std::string smt_formula = smt_str + helper_fn;

	return smt_formula;
}



std::vector<std::string> processFunctionArg(int start, int end, char** argv){
	std::vector<std::string> mocks;

	for (int i = start; i < end; ++i) {
		std::string mock_name(argv[i]);
		if (mock_name.find("--") != std::string::npos) {
		}
	}

	return mocks;
}

void processBsqFiles(ExtractorMetadata* meta){
	//TODO: Implement
	//Get the targettypes, target_info and smtformula.
}

ExtractorMetadata* processArgs(int argc, char** argv)
{
	ExtractorMetadata* meta = (ExtractorMetadata*)malloc(sizeof(ExtractorMetadata));

	for (int i = 1; i < argc; ++i) {
		std::string current_cmd(argv[i]);
		if (current_cmd.find(".bsq") != std::string::npos) {
			meta->bsq_files.push_back(current_cmd);
		}else if(current_cmd == "--functions" || current_cmd == "-f"){
			std::vector<std::string> functions = processFunctionArg(i,argc,argv);
			for (std::string fn : functions) {
				meta->mock_signatures[fn];
			}

		}else if (current_cmd == "--mock" || current_cmd == "-m") {
			meta->mode = MOCK_RUNNER;
		}else if(current_cmd == "--test" || current_cmd == "-t"){
			meta->mode = TEST_RUNNER;
		}
	}

	processBsqFiles(meta);
	assert(meta->smt_file.empty() == false && meta->type_info.empty() == false);

	return meta;
}

void extractValue(bsqon::AssemblyInfo* asm_info, ExtractSig ret, z3::solver& sol)
{
    ValueExtractor extractor(asm_info, sol);
    bsqon::Value* c_val = extractor.extractValue(ret.type, ret.ex);

    printf("Type: %s\n", (const char*)ret.type->tkey.c_str());
    printf("Value: %s\n", (const char*)c_val->toString().c_str());
}

void runMockToResult(bsqon::AssemblyInfo* asm_info, json mock_json, z3::solver& sol){
        std::string ret_id = "";
        bsqon::TypeKey tkey = mock_json["return"];
        bsqon::Type* ret_t = asm_info->lookupTypeKey(tkey);
        ret_id = "@retMock-" + tKeyToSmtName(tkey, SMT_TYPE);

        z3::check_result cr = sol.check();
        if (cr != z3::sat)
        {
            std::cout << "Got " << cr << " from .smt2 file";
            exit(1);
        }

        z3::model m = sol.get_model();

        auto const_ex = findConstantInModel(m, ret_id);
        if (!const_ex.has_value())
        {
            std::cout << "Unable to find " << ret_id << " in z3 model.\n";
            exit(1);
        }

        ExtractSig sig = {
            .type = ret_t,
            .ex = const_ex.value(),
        };

        extractValue(asm_info, sig, sol);
}

void runMockToArgs(bsqon::AssemblyInfo* asm_info, json mock_json, z3::solver& sol){
        for (auto arg : mock_json["args"])
        {
            std::string id = arg["name"];
            bsqon::TypeKey tkey = arg["type"];
            bsqon::Type* arg_t = asm_info->lookupTypeKey(tkey);

            z3::model m = sol.get_model();
            z3::expr arg_ex(sol.ctx());

            ExtractSig sig = {
                .type = arg_t,
                .ex = arg_ex,
            };

            std::string arg_id = "@arg-" + id;
            auto const_ex = findConstantInModel(m, arg_id);
            if (!const_ex.has_value())
            {
                std::cout << "Unable to find " << arg_id << " in z3 model.\n";
                exit(1);
            }

			extractValue(asm_info, sig, sol);
        }
}

int main(int argc, char** argv)
{
    if (argc != 5)
        badArgs("");

    if (argc == 4)
        badArgs("Missing --<MODE>");

    ExtractorMetadata* arg_meta = processArgs(argc, argv);

    // Load SMT FILE
	z3::context c;
	z3::solver sol(c);
    sol.from_string(arg_meta->smt_file.c_str());

    z3::check_result chk_smt = sol.check();
    if (chk_smt == z3::unsat)
    {
        badArgs("Unsat smt file\n");
    }
    else if (chk_smt == z3::unknown)
    {
        badArgs("Unknown smt file\n");
    }

    // Load TYPEINFO FILE
    bsqon::AssemblyInfo asm_info;
    json j_type;

    try
    {
        std::ifstream infile(arg_meta->type_info.c_str());
        infile >> j_type;
    }
    catch (const std::exception& e)
    {
        printf("Error parsing JSON: %s\n", e.what());
        exit(1);
    }

    bsqon::AssemblyInfo::parse(j_type, asm_info);
    bsqon::loadAssembly(j_type, asm_info);

    // Load FN INFO FILE
    for (auto& mock_sig : arg_meta->mock_signatures)
    {
        json mock_sig_json;
        try
        {
            std::ifstream infile(mock_sig.second);
            infile >> mock_sig_json;
        }
        catch (const std::exception& e)
        {
            printf("Error parsing JSON: %s\n", e.what());
            exit(1);
        }

		switch (arg_meta->mode) {
			case MOCK_RUNNER:
				runMockToResult(&asm_info, mock_sig_json, sol);
			case TEST_RUNNER:
				runMockToArgs(&asm_info, mock_sig_json, sol);
		};
    }

	Z3_finalize_memory();
	return 0;
}
