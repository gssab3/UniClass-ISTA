package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet(name = "chatServlet", value = "/chatServlet")
public class chatServlet extends HttpServlet {

    @EJB
    //@ spec_public
    //@ nullable
    private MessaggioService messaggioService;

    @EJB
    //@ spec_public
    //@ nullable
    private AccademicoService accademicoService;

    /**
     * Setter per iniettare il MessaggioService (utile per i test).
     * @param messaggioService il service da iniettare
     */
    //@ requires messaggioService != null;
    //@ ensures this.messaggioService == messaggioService;
    public void setMessaggioService(MessaggioService messaggioService) {
        this.messaggioService = messaggioService;
    }

    /**
     * Setter per iniettare l'AccademicoService (utile per i test).
     * @param accademicoService il service da iniettare
     */
    //@ requires accademicoService != null;
    //@ ensures this.accademicoService == accademicoService;
    public void setAccademicoService(AccademicoService accademicoService) {
        this.accademicoService = accademicoService;
    }

    /**
     * Gestisce le richieste GET per la chat.
     * Carica i messaggi e gli accademici coinvolti nella conversazione.
     * @param req la richiesta HTTP
     * @param resp la risposta HTTP
     */
    //@ requires req != null;
    //@ requires resp != null;
    //@ requires req.getParameter("accademico") != null;
    //@ requires req.getParameter("accademicoSelf") != null;
    @Override
    public void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            //da rivedere
            HttpSession session = req.getSession();


            String email =  req.getParameter("accademico");
            System.out.println("CHAT SERVLET email"+email);
            String emailSelf =  req.getParameter("accademicoSelf");
            System.out.println("CHAT SERVLET mia email"+email);
            Accademico accademico = accademicoService.trovaEmailUniClass(email);
            System.out.println("accademico altro: "+ accademico);
            Accademico accademicoSelf = accademicoService.trovaEmailUniClass(emailSelf);
            System.out.println("accademico self : "+ accademicoSelf);
            List<Messaggio> messaggigi = messaggioService.trovaTutti();
            System.out.println("tutti i messaggi: " + messaggigi);
            //List<Messaggio> messaggi = messaggioService.trovaMessaggi(email, emailSelf);
            //System.out.println("soli messaggi: " + messaggi);

            List<Messaggio> messaggiInviati = new ArrayList<>();
            List<Messaggio> messaggiRicevuti = new ArrayList<>();
            for(Messaggio messaggio : messaggigi) {
                if(messaggio.getDestinatario().getMatricola().equals(accademicoSelf.getMatricola())) {
                    messaggiRicevuti.add(messaggio);
                }
                if(messaggio.getAutore().getMatricola().equals(accademicoSelf.getMatricola())) {
                    messaggiInviati.add(messaggio);
                }
            }
            System.out.println("messaggi inviati: " + messaggiInviati);
            System.out.println("messaggi ricevuti: " + messaggiRicevuti);


            req.setAttribute("messaggigi", messaggigi);
            session.setAttribute("messaggigi", messaggigi);
            //req.setAttribute("messaggi", messaggi);
            req.setAttribute("messaggiInviati", messaggiInviati);
            req.setAttribute("messaggiRicevuti", messaggiRicevuti);
            req.setAttribute("accademico", accademico);
            session.setAttribute("accademico",accademico);
            session.setAttribute("accademicoSelf", accademicoSelf);
            req.setAttribute("accdemicoSelf", accademicoSelf);

            resp.sendRedirect(req.getContextPath() + "/chat.jsp");
        } catch (IOException e) {
            req.getServletContext().log("Error processing chat request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    /**
     * Gestisce le richieste POST delegando al metodo doGet.
     * @param req la richiesta HTTP
     * @param resp la risposta HTTP
     */
    //@ requires req != null;
    //@ requires resp != null;
    @Override
    public void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        doGet(req, resp);
    }
}
