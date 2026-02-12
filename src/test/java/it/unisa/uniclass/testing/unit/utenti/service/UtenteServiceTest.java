package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.common.exceptions.AlreadyExistentUserException;
import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import it.unisa.uniclass.utenti.service.dao.AccademicoRemote;
import it.unisa.uniclass.utenti.service.dao.UtenteRemote;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

/**
 * Test unitario per UtenteService.
 *
 */
@ExtendWith(MockitoExtension.class)
class UtenteServiceTest {

    @Mock
    private UtenteRemote utenteDAO;

    @Mock
    private AccademicoRemote accademicoDAO;

    @InjectMocks
    private UtenteService utenteService;

    // --- Test Login ---

    @Test
    @DisplayName("Login: Successo")
    void testLogin_Success() throws AuthenticationException {
        String email = "mario.rossi@unisa.it";
        String password = "password";
        Utente expected = new Utente();
        expected.setEmail(email);

        when(utenteDAO.login(email, password)).thenReturn(expected);

        Utente result = utenteService.login(email, password);

        assertNotNull(result);
        assertEquals(email, result.getEmail());
    }

    @Test
    @DisplayName("Login: Fallimento (Credenziali non valide)")
    void testLogin_Failure() {
        String email = "test@unisa.it";
        String password = "wrong";

        when(utenteDAO.login(email, password)).thenReturn(null);

        assertThrows(AuthenticationException.class, () -> {
            utenteService.login(email, password);
        });
    }

    // --- Test Registra Utente (Generico) ---

    @Test
    @DisplayName("Registra Utente: Successo")
    void testRegistraUtente_Success() throws AlreadyExistentUserException {
        Utente nuovoUtente = new Utente();
        nuovoUtente.setEmail("nuovo@unisa.it");

        when(utenteDAO.findByEmail("nuovo@unisa.it")).thenReturn(null);

        utenteService.registraUtente(nuovoUtente);

        // Verifica side effect: setTipo viene chiamato nel service?
        assertEquals(Tipo.Accademico, nuovoUtente.getTipo(), "Il service dovrebbe impostare il tipo di default");

        verify(utenteDAO).create(nuovoUtente);
    }

    @Test
    @DisplayName("Registra Utente: Fallimento (Già esistente)")
    void testRegistraUtente_AlreadyExists() {
        Utente utente = new Utente();
        utente.setEmail("esistente@unisa.it");

        when(utenteDAO.findByEmail("esistente@unisa.it")).thenReturn(new Utente());

        assertThrows(AlreadyExistentUserException.class, () -> {
            utenteService.registraUtente(utente);
        });

        verify(utenteDAO, never()).create(any());
    }

    // --- Test Registra Accademico ---

    @Test
    @DisplayName("Registra Accademico: Successo")
    void testRegistraAccademico_Success() throws AlreadyExistentUserException {
        Accademico accademico = new Accademico();
        accademico.setEmail("prof@unisa.it");
        Ruolo ruolo = Ruolo.DOCENTE;

        when(utenteDAO.findByEmail("prof@unisa.it")).thenReturn(null);

        utenteService.registraAccademico(accademico, ruolo);

        assertEquals(ruolo, accademico.getRuolo());
        verify(accademicoDAO).create(accademico);
    }

    @Test
    @DisplayName("Registra Accademico: Fallimento (Email occupata)")
    void testRegistraAccademico_AlreadyExists() {
        Accademico accademico = new Accademico();
        accademico.setEmail("occupata@unisa.it");

        when(utenteDAO.findByEmail("occupata@unisa.it")).thenReturn(new Utente());

        assertThrows(AlreadyExistentUserException.class, () -> {
            utenteService.registraAccademico(accademico, Ruolo.STUDENTE);
        });

        verify(accademicoDAO, never()).create(any());
    }

    // --- Test Metodi di Ricerca ---

    @Test
    @DisplayName("Get Utente By Email: Successo")
    void testGetUtenteByEmail_Success() throws NotFoundUserException {
        Utente u = new Utente();
        when(utenteDAO.findByEmail("ok@unisa.it")).thenReturn(u);

        Utente res = utenteService.getUtenteByEmail("ok@unisa.it");
        assertSame(u, res);
    }

    @Test
    @DisplayName("Get Utente By Email: Non Trovato")
    void testGetUtenteByEmail_NotFound() {
        when(utenteDAO.findByEmail("nulla@unisa.it")).thenReturn(null);

        assertThrows(NotFoundUserException.class, () -> {
            utenteService.getUtenteByEmail("nulla@unisa.it");
        });
    }

    @Test
    @DisplayName("Get Accademici Per Ruolo")
    void testGetAccademiciPerRuolo() {
        List<Accademico> list = Collections.singletonList(new Accademico());
        when(accademicoDAO.findByRole(Ruolo.STUDENTE)).thenReturn(list);

        List<Accademico> result = utenteService.getAccademiciPerRuolo(Ruolo.STUDENTE);
        assertEquals(1, result.size());
    }

    @Test
    @DisplayName("Get Tutti Gli Utenti")
    void testGetTuttiGliUtenti() {
        when(utenteDAO.findAll()).thenReturn(Collections.emptyList());
        assertTrue(utenteService.getTuttiGliUtenti().isEmpty());
    }

    // --- Test Update  ---

    @Test
    @DisplayName("Aggiorna Utente: Caso Accademico (ramo if)")
    void testAggiornaUtente_Accademico() {
        // Input è un'istanza di Accademico
        Accademico acc = new Accademico();

        utenteService.aggiornaUtente(acc);

        // Deve chiamare accademicoDAO.update, NON utenteDAO.update
        verify(accademicoDAO).update(acc);
        verify(utenteDAO, never()).update(any());
    }

    @Test
    @DisplayName("Aggiorna Utente: Caso Utente Semplice (ramo else)")
    void testAggiornaUtente_SimpleUtente() {
        // Input è un'istanza di Utente (NON Accademico)
        Utente u = new Utente();

        utenteService.aggiornaUtente(u);

        // Deve chiamare utenteDAO.update, NON accademicoDAO.update
        verify(utenteDAO).update(u);
        verify(accademicoDAO, never()).update(any());
    }
}