#include <clang/Frontend/FrontendAction.h>
#include <clang/Tooling/CompilationDatabase.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/CommandLine.h>
#include <fstream>
#include <iostream>
#include "CParser.h"
using namespace llvm;
using namespace std;
using namespace clang;
using namespace clang::tooling;
class SVASTConsumer : public ASTConsumer {
   public:
    explicit SVASTConsumer(ASTContext* context) {}

    virtual void HandleTranslationUnit(ASTContext& context) {
        Decl* rootDecl = context.getTranslationUnitDecl();
        // rootDecl->dump();
        // return;
        CParser::ParserState curState=CParser::ParserState::PREPROCESS;
        CParser preParser(&context,curState);
        preParser.TraverseDecl(rootDecl);
        curState=CParser::ParserState::PREPROCESS;
        CParser Parser(&context,curState);
        Parser.TraverseDecl(rootDecl);
        return;
    }

   private:
};

class SVFrontendAction : public ASTFrontendAction {
   protected:
    unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance& ci, StringRef) {
        return make_unique<SVASTConsumer>(&ci.getASTContext());
    }
};

// Here, I have used a set of command-line parameters specifically for SV-COMP
// verification. In the future, we anticipate expanding to more front-end
// extractions related to pointers and arrays. These parameters are primarily
// for PLDI2024.
static cl::OptionCategory SVCompCategory("the option for sv-competition");
static cl::SubCommand SVComp(
    "sv",
    "This is an option setting for validation of examples related to SVCOMP.");
static cl::opt<string> SVInputFile(cl::Positional,
                                   cl::desc("The file you want to verify."),
                                   cl::Required,
                                   cl::cat(SVCompCategory),
                                   cl::sub(SVComp));

static cl::opt<bool> SVPropagation("prop",
                                   cl::desc("The file you want to verify."),
                                   cl::init(false),
                                   cl::cat(SVCompCategory),
                                   cl::sub(SVComp));

#ifndef USE_LSTINGX_MAIN
int main(int argc, const char** argv) {
    cl::HideUnrelatedOptions(SVCompCategory);
    cl::ParseCommandLineOptions(argc, argv);
    if (SVComp) {
        string inputFile = SVInputFile.getValue();
        vector<string> sources;
        cout << inputFile << endl;
        sources.push_back(inputFile);
        string errorMsg;
        int remainingArgc = argc;
        auto compilationDB = FixedCompilationDatabase::loadFromCommandLine(
            remainingArgc, argv, errorMsg);
        if (!compilationDB) {
            outs() << "[info] Using default compilation options.\n";
            SmallString<256> currentDir;
            sys::fs::current_path(currentDir);
            compilationDB = make_unique<FixedCompilationDatabase>(
                Twine(currentDir), ArrayRef<string>());
        }

        ClangTool tool(*compilationDB, sources);
        return tool.run(newFrontendActionFactory<SVFrontendAction>().get());
    }
    perror(
        "Please choose at least one from the following command modes: [--sv]");
}
#endif