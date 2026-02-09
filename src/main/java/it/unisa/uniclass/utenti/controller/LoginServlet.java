package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.PersonaleTA;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.servlet.annotation.*;
import jakarta.servlet.http.*;

import java.io.IOException;

@WebServlet(name = "loginServlet", value = "/Login")
public class LoginServlet extends HttpServlet{


    private AccademicoService accademicoService;
    private PersonaleTAService personaleTAService;

    public void setAccademicoService(AccademicoService accademicoService) {
        this.accademicoService = accademicoService;
    }

    public void setPersonaleTAService(PersonaleTAService personaleTAService) {
        this.personaleTAService = personaleTAService;
    }

    protected AccademicoService getAccademicoService() {
        return new AccademicoService();
    }

    protected PersonaleTAService getPersonaleTAService() {
        return new PersonaleTAService();
    }


    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            if(accademicoService == null) {
                accademicoService = new AccademicoService();
            }
            if(personaleTAService == null) {
                personaleTAService = new PersonaleTAService();
            }
            String email = request.getParameter("email");
            //Password non hashata, così come viene digitata
            String password = request.getParameter("password");

            //password hashata, da come viene digitata all'hashing
            password = CredentialSecurity.hashPassword(password);
            Accademico user1 = accademicoService.trovaEmailPassUniclass(email, password);
            PersonaleTA user2 = personaleTAService.trovaEmailPass(email,password);
            Utente user = null;


            /*
            Si deve prima cercare di capire quale user è null. Quello non null bisogna vedere se è accademico (in quel caso controllare se
            è attivato, altrimenti senza password c'è errore), altrimenti vedere se è personaleTA (esso non viene attivato, c'è e basta)
             */
            if(user1 == null && user2 == null){
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
                return;
            } else if(user1 != null && user2 == null){
                if(user1.isAttivato()) {
                    user = user1;
                }else if(user1.getPassword() == null){
                    response.sendRedirect(request.getContextPath() + "/Login.jsp?action=notactivated");
                    return;
                }
            } else if(user1 == null && user2 != null) {
                user = user2;
            }


            if (user != null) {
                HttpSession session = request.getSession(true);
                session.setAttribute("currentSessionUser", user);
                response.sendRedirect(request.getContextPath() + "/Home");
                return;
            } else {
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
                return;
            }
        } catch (IOException e) {
            request.getServletContext().log("Error processing login request", e);
            try {
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
            } catch (IOException ioException) {
                request.getServletContext().log("Failed to redirect after error", ioException);
            }
        }
    }
}
