package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.common.security.PasswordGenerator;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Tipo;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

@WebServlet(name = "AttivaUtentiServlet", value = "/AttivaUtentiServlet")
public class AttivaUtentiServlet extends HttpServlet {

    private AccademicoService accademicoService;

    // This method is added for testing purposes
    public void setAccademicoService(AccademicoService accademicoService) {
        this.accademicoService = accademicoService;
    }

    public AttivaUtentiServlet() {
        accademicoService = new AccademicoService();
    }

    public AttivaUtentiServlet(AccademicoService acc) {
        accademicoService = acc;
    }

    // This method is added for testing purposes
    public void doPostPublic(HttpServletRequest req, HttpServletResponse resp) {
        doPost(req, resp);
    }

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        doPost(req, resp);
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        try {
            String param = req.getParameter("param");

            if(param.equals("add")){
                String email = (String) req.getParameter("email");
                String matricola = (String) req.getParameter("matricola");
                String tiporeq = (String) req.getParameter("tipo");

                Accademico accademicoEmail = accademicoService.trovaEmailUniClass(email);
                Accademico accademicoMatricola = accademicoService.trovaAccademicoUniClass(matricola);
                Accademico accademico = null;
                Tipo tipo = null;
                if(tiporeq.equals("Studente")) {
                    tipo = Tipo.Studente;
                }
                else if(tiporeq.equals("Docente")) {
                    tipo = Tipo.Docente;
                }
                else if(tiporeq.equals("Coordinatore")) {
                    tipo = Tipo.Coordinatore;
                }

                if(accademicoEmail != null && accademicoMatricola != null &&
                        accademicoEmail.getEmail().equals(accademicoMatricola.getEmail()) &&
                        accademicoEmail.getMatricola().equals(accademicoMatricola.getMatricola())){
                    if(accademicoEmail.getTipo().equals(tipo)) {
                        accademico = accademicoEmail;
                        String password = PasswordGenerator.generatePassword(8);

                        accademico.setAttivato(true);
                        accademico.setPassword(CredentialSecurity.hashPassword(password));

                        accademicoService.aggiungiAccademico(accademico);
                        System.out.println("\n\n\nPassword generata per l'attivato: " + password + "\n\n\n");
                        resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp");
                    } else {
                        resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp?action=error");
                    }
                } else {
                    resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp?action=error");
                }
            } else if(param.equals("remove")){
                String email = (String) req.getParameter("email-remove");

                Accademico accademico = accademicoService.trovaEmailUniClass(email);
                if (accademico != null) {
                    accademicoService.cambiaAttivazione(accademico, false);
                }
                resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp");
            }
        } catch (IOException e) {
            req.getServletContext().log("Error processing user activation request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }
}
