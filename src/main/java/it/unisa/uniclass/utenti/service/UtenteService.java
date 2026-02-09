package it.unisa.uniclass.utenti.service;

import it.unisa.uniclass.common.exceptions.AlreadyExistentUserException;
import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.dao.AccademicoRemote;
import it.unisa.uniclass.utenti.service.dao.UtenteRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;

import java.util.List;

@Stateless
public class UtenteService {

    @EJB(beanName = "UtenteDAO")
    private UtenteRemote utenteDAO;

    @EJB(beanName = "AccademicoDAO")
    private AccademicoRemote accademicoDAO;

    // --- AUTENTICAZIONE ---

    public Utente login(String email, String password) throws AuthenticationException {
        Utente u = utenteDAO.login(email, password);
        if (u == null) {
            throw new AuthenticationException("Credenziali non valide.");
        }
        return u;
    }

    // --- GESTIONE UTENTI GENERICI (Ex Personale TA) ---

    /**
     * Registra un utente generico (es. Personale Amministrativo).
     * Non avendo un ruolo accademico, viene persistito nella tabella Utente.
     */
    public void registraUtente(Utente utente) throws AlreadyExistentUserException {
        if (utenteDAO.findByEmail(utente.getEmail()) != null) {
            throw new AlreadyExistentUserException("Utente già esistente: " + utente.getEmail());
        }
        // Qui potresti settare un 'tipo' di default se il DB lo richiede, es:
        // utente.setTipo("AMMINISTRATIVO");
        utenteDAO.create(utente);
    }

    // --- GESTIONE ACCADEMICI (Studenti, Docenti, Coordinatori) ---

    public void registraAccademico(Accademico accademico, Ruolo ruolo) throws AlreadyExistentUserException {
        if (utenteDAO.findByEmail(accademico.getEmail()) != null) {
            throw new AlreadyExistentUserException("Email già presente nel sistema.");
        }

        // Impostiamo il ruolo (enum Ruolo)
        accademico.setRuolo(ruolo);

        // Salviamo tramite il DAO specifico che gestisce la tabella estesa
        accademicoDAO.create(accademico);
    }

    // --- METODI DI RICERCA ---

    public Utente getUtenteByEmail(String email) throws NotFoundUserException {
        Utente u = utenteDAO.findByEmail(email);
        if (u == null) {
            throw new NotFoundUserException("Utente non trovato.");
        }
        return u;
    }

    /**
     * Restituisce tutti gli accademici filtrati per ruolo.
     * Utile per le liste (es. "Mostra tutti gli Studenti").
     */
    public List<Accademico> getAccademiciPerRuolo(Ruolo ruolo) {
        return accademicoDAO.findByRole(ruolo);
    }

    public List<Utente> getTuttiGliUtenti() {
        return utenteDAO.findAll();
    }

    // --- UPDATE ---

    public void aggiornaUtente(Utente utente) {
        // Se l'oggetto è un'istanza di Accademico, usiamo il suo DAO per fare il merge corretto di tutti i campi
        if (utente instanceof Accademico) {
            accademicoDAO.update((Accademico) utente);
        } else {
            utenteDAO.update(utente);
        }
    }
}